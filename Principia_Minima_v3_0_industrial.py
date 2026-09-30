import os
import re
import time
import json
import math
import sqlite3
import uuid
import base64
import html
import webbrowser
from pathlib import Path
from datetime import datetime, timedelta
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

import pandas as pd
import numpy as np
from ortools.linear_solver import pywraplp


# =====================================================================
# PRINCIPIA MINIMA - VERSAO 3.2 FACTORY INTELLIGENCE
# Otimizacao de corte de barras de cobre
#
# MODOS:
# 1) PLANEJADO:
#    - entrada: demanda futura (CSV)
#    - considera barras novas padrao
#    - objetivo 1: minimizar quantidade de barras
#    - objetivo 2: manter minimo de barras e minimizar desperdicio real
#
# 2) EMERGENCIAL:
#    - entrada: demanda semanal (CSV) + estoque atual informado manualmente
#      e/ou por planilha CSV
#    - considera barras novas e retalhos de diferentes comprimentos
#    - proibe sobreproducao
#    - se faltar material, informa o que nao foi atendido
#    - entre solucoes com o mesmo atendimento, minimiza o comprimento
#      total retirado do estoque (aproveitamento global)
#    - se ainda houver falta, gera plano otimizado com barras padrao para completar a demanda
#
# FORMATO PREFERENCIAL DA DEMANDA:
# PIV;LINHA;DIAMETRO;COMPRIMENTO;DEMANDA
# 43174;10;30;987;5
# 43174;20;30;620;8
# 43287;10;42;850;4
#
# Tambem aceita o formato legado:
# DIAMETRO;COMPRIMENTO;DEMANDA
#
# ESTOQUE EMERGENCIAL:
# Informado diretamente na tela e/ou por planilha:
# DIAMETRO | COMPRIMENTO | QUANTIDADE
# O sistema classifica como NOVA quando o comprimento for igual a barra padrao;
# os demais comprimentos sao tratados como RETALHO.
# =====================================================================


# ---------------------------------------------------------------------
# PARAMETROS PADRAO
# ---------------------------------------------------------------------
BARRA_PADRAO_DEFAULT = 3500.0
KERF_DEFAULT = 5
LIMITE_RETALHO_DEFAULT = 700.0
DESPERDICIO_MAX_RECOMENDADO_DEFAULT = 250.0
TEMPO_LIMITE_OTIMIZACAO_MS = 240000  # 60 segundos por diametro


# =====================================================================
# UTILIDADES DE DADOS
# =====================================================================

def _normalizar_numero(serie):
    """Converte valores numericos aceitando ponto ou virgula decimal."""
    return pd.to_numeric(
        serie.astype(str)
        .str.strip()
        .str.replace("Ø", "", regex=False)
        .str.replace(",", ".", regex=False),
        errors="coerce",
    )


def ler_demanda_csv(caminho):
    """
    Le a demanda preservando PIV e LINHA para rastreabilidade.

    Formato preferencial:
        PIV;LINHA;DIAMETRO;COMPRIMENTO;DEMANDA

    Por compatibilidade, tambem aceita:
        DIAMETRO;COMPRIMENTO;DEMANDA

    A agregacao por diametro/comprimento e feita separadamente para o solver,
    evitando aumentar desnecessariamente o problema matematico.
    """
    df = pd.read_csv(caminho, sep=";", dtype=str)
    df.columns = df.columns.str.strip().str.upper()

    necessarias = {"DIAMETRO", "COMPRIMENTO", "DEMANDA"}
    if not necessarias.issubset(df.columns):
        raise ValueError(
            "A planilha de demanda deve possuir, no minimo, as colunas:\n"
            "DIAMETRO;COMPRIMENTO;DEMANDA\n\n"
            "Para rastreabilidade, utilize preferencialmente:\n"
            "PIV;LINHA;DIAMETRO;COMPRIMENTO;DEMANDA\n\n"
            f"Colunas encontradas: {list(df.columns)}"
        )

    # Mantem compatibilidade com arquivos antigos.
    if "PIV" not in df.columns:
        df["PIV"] = "SEM_PIV"
    if "LINHA" not in df.columns:
        df["LINHA"] = "SEM_LINHA"

    df = df[["PIV", "LINHA", "DIAMETRO", "COMPRIMENTO", "DEMANDA"]].copy()

    # Preserva a ordem original para alocacao FIFO posterior.
    df["_ORDEM"] = range(len(df))

    # Remove somente linhas sem informacao fisica/demanda.
    df = df.dropna(subset=["DIAMETRO", "COMPRIMENTO", "DEMANDA"])
    if df.empty:
        raise ValueError("A planilha de demanda esta vazia.")

    df["PIV"] = df["PIV"].fillna("SEM_PIV").astype(str).str.strip()
    df["LINHA"] = df["LINHA"].fillna("SEM_LINHA").astype(str).str.strip()

    df.loc[df["PIV"] == "", "PIV"] = "SEM_PIV"
    df.loc[df["LINHA"] == "", "LINHA"] = "SEM_LINHA"

    df["DIAMETRO"] = _normalizar_numero(df["DIAMETRO"])
    df["COMPRIMENTO"] = _normalizar_numero(df["COMPRIMENTO"])
    df["DEMANDA"] = _normalizar_numero(df["DEMANDA"])

    if df[["DIAMETRO", "COMPRIMENTO", "DEMANDA"]].isna().any().any():
        raise ValueError(
            "Existem valores invalidos na demanda. "
            "Verifique diametro, comprimento e demanda."
        )

    if (df["DIAMETRO"] <= 0).any() or (df["COMPRIMENTO"] <= 0).any():
        raise ValueError("Diametro e comprimento devem ser positivos.")

    if (df["DEMANDA"] <= 0).any():
        raise ValueError("A demanda deve ser maior que zero.")

    if ((df["DEMANDA"] % 1) != 0).any():
        raise ValueError("A coluna DEMANDA deve conter apenas numeros inteiros.")

    df["DEMANDA"] = df["DEMANDA"].astype(int)
    df["DIAMETRO"] = df["DIAMETRO"].round(4)
    df["COMPRIMENTO"] = df["COMPRIMENTO"].round(4)

    return df.sort_values("_ORDEM").reset_index(drop=True)


def agrupar_demanda_para_solver(df_demanda_detalhada):
    """
    Consolida a demanda somente para o modelo matematico.
    PIV e LINHA permanecem no dataframe detalhado para rastreabilidade.
    """
    return (
        df_demanda_detalhada
        .groupby(["DIAMETRO", "COMPRIMENTO"], as_index=False)["DEMANDA"]
        .sum()
        .sort_values(["DIAMETRO", "COMPRIMENTO"], ascending=[True, False])
        .reset_index(drop=True)
    )


def ler_estoque_csv(caminho, barra_padrao):
    """
    Le estoque emergencial em CSV.

    Formato:
        DIAMETRO;COMPRIMENTO;QUANTIDADE

    O TIPO e inferido automaticamente:
    - comprimento igual a barra padrao -> NOVA
    - demais comprimentos -> RETALHO
    """
    df = pd.read_csv(caminho, sep=";", dtype=str)
    df.columns = df.columns.str.strip().str.upper()

    necessarias = {"DIAMETRO", "COMPRIMENTO", "QUANTIDADE"}
    if not necessarias.issubset(df.columns):
        raise ValueError(
            "A planilha de estoque deve possuir as colunas:\n"
            "DIAMETRO;COMPRIMENTO;QUANTIDADE\n\n"
            f"Colunas encontradas: {list(df.columns)}"
        )

    df = df[["DIAMETRO", "COMPRIMENTO", "QUANTIDADE"]].dropna()
    if df.empty:
        raise ValueError("A planilha de estoque esta vazia.")

    df["DIAMETRO"] = _normalizar_numero(df["DIAMETRO"])
    df["COMPRIMENTO"] = _normalizar_numero(df["COMPRIMENTO"])
    df["QUANTIDADE"] = _normalizar_numero(df["QUANTIDADE"])

    if df[["DIAMETRO", "COMPRIMENTO", "QUANTIDADE"]].isna().any().any():
        raise ValueError(
            "Existem valores numericos invalidos no estoque. "
            "Verifique diametro, comprimento e quantidade."
        )

    if (
        (df["DIAMETRO"] <= 0).any()
        or (df["COMPRIMENTO"] <= 0).any()
        or (df["QUANTIDADE"] <= 0).any()
    ):
        raise ValueError("Os valores do estoque devem ser positivos.")

    if ((df["QUANTIDADE"] % 1) != 0).any():
        raise ValueError("A coluna QUANTIDADE deve conter apenas numeros inteiros.")

    df["QUANTIDADE"] = df["QUANTIDADE"].astype(int)
    df["DIAMETRO"] = df["DIAMETRO"].round(4)
    df["COMPRIMENTO"] = df["COMPRIMENTO"].round(4)

    df["TIPO"] = df["COMPRIMENTO"].apply(
        lambda c: "NOVA"
        if abs(float(c) - float(barra_padrao)) <= 1e-6
        else "RETALHO"
    )

    return (
        df.groupby(["TIPO", "DIAMETRO", "COMPRIMENTO"], as_index=False)["QUANTIDADE"]
        .sum()
        .sort_values(
            ["DIAMETRO", "TIPO", "COMPRIMENTO"],
            ascending=[True, True, False],
        )
        .reset_index(drop=True)
    )


def _extrair_cortes_do_esquema(esquema):
    """
    Converte:
        '2x(987mm) + 1x(620mm)'
    em:
        [(987.0, 2), (620.0, 1)]
    """
    if not isinstance(esquema, str):
        return []

    cortes = []
    for qtd, comp in re.findall(
        r"(\d+)x\(([-+]?\d+(?:[.,]\d+)?)mm\)",
        esquema,
        flags=re.IGNORECASE,
    ):
        cortes.append((float(comp.replace(",", ".")), int(qtd)))
    return cortes


def adicionar_rastreabilidade_ao_plano(plano, demanda_detalhada):
    """
    Expande cada padrao para uma linha por barra fisica e aloca as pecas
    aos PIVs/LINHAs em ordem FIFO, sem alterar a solucao matematica.

    O solver continua trabalhando com demanda agregada por
    DIAMETRO + COMPRIMENTO.
    """
    if plano.empty:
        return plano.copy()

    # Fila FIFO para cada combinacao fisica.
    filas = {}
    demanda_ord = demanda_detalhada.sort_values("_ORDEM").copy()

    for _, row in demanda_ord.iterrows():
        chave = (round(float(row["DIAMETRO"]), 4), round(float(row["COMPRIMENTO"]), 4))
        filas.setdefault(chave, []).append(
            {
                "PIV": str(row["PIV"]),
                "LINHA": str(row["LINHA"]),
                "restante": int(row["DEMANDA"]),
            }
        )

    linhas_expandidas = []
    contador_barra = 1

    for _, row in plano.iterrows():
        qtd_barras = int(row.get("QTD_BARRAS", 1))
        cortes = _extrair_cortes_do_esquema(row.get("ESQUEMA_DE_CORTE", ""))

        for repeticao in range(1, qtd_barras + 1):
            nova = row.to_dict()
            nova["QTD_BARRAS"] = 1
            nova["ID_PADRAO_ORIGINAL"] = nova.get("ID_PADRAO", "")
            nova["ID_BARRA"] = f"B{contador_barra:04d}"

            referencias = []

            for comp, qtd in cortes:
                chave = (
                    round(float(row["DIAMETRO"]), 4),
                    round(float(comp), 4),
                )

                fila = filas.get(chave, [])
                faltam_alocar = qtd

                while faltam_alocar > 0 and fila:
                    pedido = fila[0]
                    usar = min(faltam_alocar, pedido["restante"])

                    referencias.append(
                        {
                            "PIV": pedido["PIV"],
                            "LINHA": pedido["LINHA"],
                            "COMPRIMENTO": comp,
                            "QTD": usar,
                        }
                    )

                    pedido["restante"] -= usar
                    faltam_alocar -= usar

                    if pedido["restante"] <= 0:
                        fila.pop(0)

                if faltam_alocar > 0:
                    # Mantem o plano exportavel mesmo se a rastreabilidade
                    # estiver incompleta no arquivo de origem.
                    referencias.append(
                        {
                            "PIV": "SEM_REFERENCIA",
                            "LINHA": "SEM_REFERENCIA",
                            "COMPRIMENTO": comp,
                            "QTD": faltam_alocar,
                        }
                    )

            # Consolida referencias iguais dentro da mesma barra.
            consolidadas = []
            mapa = {}
            for ref in referencias:
                chave_ref = (
                    ref["PIV"],
                    ref["LINHA"],
                    round(ref["COMPRIMENTO"], 4),
                )
                if chave_ref not in mapa:
                    mapa[chave_ref] = len(consolidadas)
                    consolidadas.append(ref.copy())
                else:
                    consolidadas[mapa[chave_ref]]["QTD"] += ref["QTD"]

            nova["PIV_LINHAS_ATENDIDAS"] = "; ".join(
                (
                    f"PIV {ref['PIV']} / Linha {ref['LINHA']} -> "
                    f"{ref['QTD']}x({ref['COMPRIMENTO']:g}mm)"
                )
                for ref in consolidadas
            )

            linhas_expandidas.append(nova)
            contador_barra += 1

    resultado = pd.DataFrame(linhas_expandidas)

    # Posiciona identificadores e rastreabilidade perto do inicio da planilha.
    colunas_prioritarias = [
        "MODO",
        "DIAMETRO",
        "ID_BARRA",
        "ID_PADRAO",
        "ID_PADRAO_ORIGINAL",
        "TIPO_FONTE",
        "COMPRIMENTO_FONTE_MM",
        "QTD_BARRAS",
        "ESQUEMA_DE_CORTE",
        "PIV_LINHAS_ATENDIDAS",
        "SOBRA_POR_BARRA_MM",
        "CLASSIFICACAO_SOBRA",
        "ORIGEM_PLANO",
    ]

    existentes = [c for c in colunas_prioritarias if c in resultado.columns]
    restantes = [c for c in resultado.columns if c not in existentes]
    return resultado[existentes + restantes]


# =====================================================================
# GERACAO DE PADROES
# =====================================================================

def gerar_padroes_completos(comprimentos_nominais, demandas, tamanho_fonte, kerf):
    """
    Gera todos os padroes nao vazios que cabem na fonte.

    Diferente da versao antiga, NAO exige que o padrao seja maximal.
    Isso e necessario para permitir atendimento exato da demanda sem
    sobreproducao.
    """
    reais = [round(c + kerf, 6) for c in comprimentos_nominais]
    padroes = []
    atual = [0] * len(comprimentos_nominais)

    def rec(indice, restante):
        if indice == len(reais):
            if sum(atual) > 0:
                padroes.append(tuple(atual))
            return

        max_por_espaco = int((restante + 1e-9) // reais[indice])
        max_qtd = min(max_por_espaco, int(demandas[indice]))

        for qtd in range(max_qtd, -1, -1):
            atual[indice] = qtd
            rec(indice + 1, restante - qtd * reais[indice])

        atual[indice] = 0

    rec(0, float(tamanho_fonte))

    # remove duplicatas preservando ordem
    return list(dict.fromkeys(padroes))


def calcular_sobra(padrao, comprimentos_nominais, tamanho_fonte, kerf):
    consumido = sum(
        qtd * (comp + kerf)
        for qtd, comp in zip(padrao, comprimentos_nominais)
    )
    return round(tamanho_fonte - consumido, 4)


def criar_solver(nome="SCIP"):
    solver = pywraplp.Solver.CreateSolver(nome)
    if solver is None:
        solver = pywraplp.Solver.CreateSolver("CBC")
    if solver is None:
        raise RuntimeError(
            "Nenhum solver inteiro disponivel no OR-Tools. "
            "Verifique a instalacao do pacote."
        )
    return solver


def tempo_restante_otimizacao_ms(inicio_otimizacao):
    """
    Retorna o tempo restante do orçamento total de otimização.

    O limite é compartilhado entre a Etapa 1 e a Etapa 2.
    Assim, cada diâmetro recebe no máximo 60 segundos de busca do solver.
    """
    decorrido_ms = int((time.monotonic() - inicio_otimizacao) * 1000)
    return max(0, TEMPO_LIMITE_OTIMIZACAO_MS - decorrido_ms)


# =====================================================================
# MOTOR PLANEJADO
# =====================================================================

def otimizar_planejado_por_diametro(
    diametro,
    df_demanda_diametro,
    tamanho_barra,
    kerf,
    limite_retalho,
    desperdicio_max_recomendado,
):
    comprimentos = sorted(
        df_demanda_diametro["COMPRIMENTO"].astype(float).tolist(),
        reverse=True,
    )
    demanda_map = dict(
        zip(
            df_demanda_diametro["COMPRIMENTO"].astype(float),
            df_demanda_diametro["DEMANDA"].astype(int),
        )
    )
    demandas = [demanda_map[c] for c in comprimentos]

    invalidas = [c for c in comprimentos if c + kerf > tamanho_barra]
    if invalidas:
        raise ValueError(
            f"Diametro {diametro}: existem pecas maiores que a barra padrao "
            f"de {tamanho_barra} mm: {invalidas}"
        )

    padroes = gerar_padroes_completos(
        comprimentos,
        demandas,
        tamanho_barra,
        kerf,
    )

    if not padroes:
        raise RuntimeError(f"Diametro {diametro}: nenhum padrao viavel foi gerado.")

    sobras = [
        calcular_sobra(p, comprimentos, tamanho_barra, kerf) for p in padroes
    ]
    desperdicios = [s if s < limite_retalho else 0.0 for s in sobras]

    # Preferencia suave:
    # padroes acima do desperdicio maximo recomendado continuam permitidos,
    # mas recebem uma penalidade adicional no objetivo.
    excessos_recomendados = [
        max(0.0, d - desperdicio_max_recomendado)
        for d in desperdicios
    ]
    custos_desperdicio = [
        d + excesso
        for d, excesso in zip(desperdicios, excessos_recomendados)
    ]

    # ---------------------------------------------------------
    # ORCAMENTO TOTAL DE OTIMIZACAO: 60 segundos por diametro
    # ---------------------------------------------------------
    inicio_otimizacao = time.monotonic()

    # ---------------------------
    # ETAPA 1: minimo de barras
    # ---------------------------
    solver1 = criar_solver()
    x1 = [
        solver1.IntVar(0, solver1.infinity(), f"x1_{j}")
        for j in range(len(padroes))
    ]

    for i, demanda in enumerate(demandas):
        solver1.Add(
            solver1.Sum(
                padroes[j][i] * x1[j]
                for j in range(len(padroes))
            )
            == demanda
        )

    solver1.Minimize(solver1.Sum(x1))
    solver1.SetTimeLimit(
        max(1, tempo_restante_otimizacao_ms(inicio_otimizacao))
    )

    status1 = solver1.Solve()

    if status1 not in (pywraplp.Solver.OPTIMAL, pywraplp.Solver.FEASIBLE):
        raise RuntimeError(
            f"Diametro {diametro}: nenhuma solucao viavel foi encontrada "
            "dentro do limite de 60 segundos."
        )

    minimo_barras = int(round(solver1.Objective().Value()))
    valores_etapa1 = [
        int(round(v.solution_value()))
        for v in x1
    ]

    # Se a Etapa 1 atingiu o limite antes de provar o ótimo,
    # preserva a melhor solução viável encontrada.
    if status1 != pywraplp.Solver.OPTIMAL:
        valores = valores_etapa1
        status_texto = (
            "Melhor solucao viavel encontrada em ate 240 segundos; "
            "minimo de barras nao comprovado"
        )

    # Se o objetivo principal foi provado ótimo, usa o tempo que restou
    # para procurar a combinação de menor desperdício.
    elif tempo_restante_otimizacao_ms(inicio_otimizacao) <= 0:
        valores = valores_etapa1
        status_texto = (
            "Otimo em numero de barras; limite total de 240 segundos "
            "atingido antes do refinamento de desperdicio"
        )

    else:
        # ---------------------------
        # ETAPA 2: minimo desperdicio
        # ---------------------------
        solver2 = criar_solver()
        x2 = [
            solver2.IntVar(0, solver2.infinity(), f"x2_{j}")
            for j in range(len(padroes))
        ]

        for i, demanda in enumerate(demandas):
            solver2.Add(
                solver2.Sum(
                    padroes[j][i] * x2[j]
                    for j in range(len(padroes))
                )
                == demanda
            )

        solver2.Add(solver2.Sum(x2) == minimo_barras)
        solver2.Minimize(
            solver2.Sum(
                custos_desperdicio[j] * x2[j]
                for j in range(len(padroes))
            )
        )

        try:
            solver2.SetHint(
                x2,
                [v.solution_value() for v in x1],
            )
        except Exception:
            pass

        tempo_restante = tempo_restante_otimizacao_ms(inicio_otimizacao)

        if tempo_restante <= 0:
            valores = valores_etapa1
            status_texto = (
                "Otimo em numero de barras; limite total de 60 segundos "
                "atingido antes da Etapa 2"
            )
        else:
            solver2.SetTimeLimit(tempo_restante)
            status2 = solver2.Solve()

            if status2 not in (
                pywraplp.Solver.OPTIMAL,
                pywraplp.Solver.FEASIBLE,
            ):
                valores = valores_etapa1
                status_texto = (
                    "Otimo em numero de barras; melhor solucao da Etapa 1 "
                    "mantida ao atingir o limite de 60 segundos"
                )
            else:
                valores = [
                    int(round(v.solution_value()))
                    for v in x2
                ]
                status_texto = (
                    "Ótima comprovada | política: bons retalhos → barras novas do estoque → retalhos de baixa qualidade"
                    if status2 == pywraplp.Solver.OPTIMAL
                    else "Melhor solução viável | política: bons retalhos → barras novas do estoque → retalhos de baixa qualidade"
                )

    linhas_plano = []
    total_desperdicio = 0.0
    total_retalho = 0.0
    total_sobra = 0.0
    id_padrao = 1

    for j, vezes in enumerate(valores):
        if vezes <= 0:
            continue

        padrao = padroes[j]
        sobra = sobras[j]

        total_sobra += sobra * vezes
        if sobra >= limite_retalho:
            total_retalho += sobra * vezes
            classificacao = "RETALHO REAPROVEITAVEL"
        else:
            total_desperdicio += sobra * vezes
            classificacao = "DESPERDICIO"

        partes = []
        for qtd, comp in zip(padrao, comprimentos):
            if qtd > 0:
                partes.append(f"{qtd}x({comp:g}mm)")

        linhas_plano.append(
            {
                "MODO": "PLANEJADO",
                "DIAMETRO": diametro,
                "ID_PADRAO": f"P{diametro:g}-{id_padrao}",
                "TIPO_FONTE": "NOVA",
                "COMPRIMENTO_FONTE_MM": tamanho_barra,
                "QTD_BARRAS": vezes,
                "ESQUEMA_DE_CORTE": " + ".join(partes),
                "SOBRA_POR_BARRA_MM": sobra,
                "CLASSIFICACAO_SOBRA": classificacao,
            }
        )
        id_padrao += 1

    demanda_total_mm = sum(c * d for c, d in zip(comprimentos, demandas))
    material_total_mm = minimo_barras * tamanho_barra
    aproveitamento_percentual = (
        100.0 * demanda_total_mm / material_total_mm
        if material_total_mm > 0
        else 0.0
    )
    retalhos_gerados_barras = sum(
        int(vezes)
        for j, vezes in enumerate(valores)
        if vezes > 0 and sobras[j] >= limite_retalho
    )

    barras_acima_desperdicio_recomendado = sum(
        int(vezes)
        for j, vezes in enumerate(valores)
        if vezes > 0 and desperdicios[j] > desperdicio_max_recomendado
    )
    maior_desperdicio_por_barra = max(
        (
            desperdicios[j]
            for j, vezes in enumerate(valores)
            if vezes > 0
        ),
        default=0.0,
    )

    resumo = {
        "DIAMETRO": diametro,
        "DEMANDA_TOTAL_PECAS": int(sum(demandas)),
        "DEMANDA_TOTAL_MM": round(demanda_total_mm, 2),
        "PECAS_ATENDIDAS": int(sum(demandas)),
        "PECAS_FALTANTES": 0,
        "BARRAS_NOVAS_USADAS": minimo_barras,
        "RETALHOS_USADOS": 0,
        "TOTAL_FONTES_USADAS": minimo_barras,
        "SOBRA_FISICA_TOTAL_MM": round(total_sobra, 2),
        "DESPERDICIO_REAL_MM": round(total_desperdicio, 2),
        "DESPERDICIO_MAX_RECOMENDADO_MM": round(desperdicio_max_recomendado, 2),
        "BARRAS_ACIMA_DESPERDICIO_RECOMENDADO": barras_acima_desperdicio_recomendado,
        "MAIOR_DESPERDICIO_POR_BARRA_MM": round(maior_desperdicio_por_barra, 2),
        "RETALHO_REAPROVEITAVEL_BARRAS": retalhos_gerados_barras,
        "RETALHO_REAPROVEITAVEL_MM": round(total_retalho, 2),
        "APROVEITAMENTO_PERCENTUAL": round(aproveitamento_percentual, 2),
        "STATUS": status_texto,
        "PADROES_GERADOS": len(padroes),
    }

    return linhas_plano, resumo


def executar_planejado(df_demanda, tamanho_barra, kerf, limite_retalho, desperdicio_max_recomendado):
    plano_total = []
    resumos = []

    for diametro in sorted(df_demanda["DIAMETRO"].unique()):
        grupo = df_demanda[df_demanda["DIAMETRO"] == diametro].copy()
        linhas, resumo = otimizar_planejado_por_diametro(
            diametro,
            grupo,
            tamanho_barra,
            kerf,
            limite_retalho,
            desperdicio_max_recomendado,
        )
        plano_total.extend(linhas)
        resumos.append(resumo)

    return pd.DataFrame(plano_total), pd.DataFrame(resumos)


# =====================================================================
# MOTOR EMERGENCIAL
# =====================================================================

def otimizar_emergencial_por_diametro(
    diametro,
    df_demanda_diametro,
    df_estoque_diametro,
    kerf,
    limite_retalho,
    desperdicio_max_recomendado,
    barra_padrao_recomendacao,
):
    comprimentos = sorted(
        df_demanda_diametro["COMPRIMENTO"].astype(float).tolist(),
        reverse=True,
    )
    demanda_map = dict(
        zip(
            df_demanda_diametro["COMPRIMENTO"].astype(float),
            df_demanda_diametro["DEMANDA"].astype(int),
        )
    )
    demandas = [demanda_map[c] for c in comprimentos]

    classes = []
    if not df_estoque_diametro.empty:
        for _, row in df_estoque_diametro.iterrows():
            classes.append(
                {
                    "tipo": row["TIPO"],
                    "comprimento": float(row["COMPRIMENTO"]),
                    "quantidade": int(row["QUANTIDADE"]),
                }
            )

    # Padroes por classe de estoque
    padroes_por_classe = []
    for s, classe in enumerate(classes):
        padroes = gerar_padroes_completos(
            comprimentos,
            demandas,
            classe["comprimento"],
            kerf,
        )

        registros = []
        for p in padroes:
            sobra = calcular_sobra(p, comprimentos, classe["comprimento"], kerf)
            desperdicio = sobra if sobra < limite_retalho else 0.0
            excesso_recomendado = max(
                0.0,
                desperdicio - desperdicio_max_recomendado,
            )
            # Política emergencial V3.2:
            # - um padrão de retalho é considerado preferencial quando gera
            #   desperdício <= limite recomendado OU deixa sobra reaproveitável;
            # - barras NOVAS permanecem disponíveis como segunda alternativa;
            # - padrões ruins de retalho continuam permitidos como último recurso.
            padrao_preferencial = (
                sobra >= limite_retalho
                or desperdicio <= desperdicio_max_recomendado
            )
            registros.append(
                {
                    "padrao": p,
                    "sobra": sobra,
                    "desperdicio": desperdicio,
                    "excesso_recomendado": excesso_recomendado,
                    "padrao_preferencial": bool(padrao_preferencial),
                }
            )

        padroes_por_classe.append(registros)

    # Se nao houver qualquer padrao viavel, toda a demanda fica faltante
    total_padroes = sum(len(x) for x in padroes_por_classe)

    if total_padroes == 0:
        faltas = [
            {"DIAMETRO": diametro, "COMPRIMENTO": c, "QTD_FALTANTE": d}
            for c, d in zip(comprimentos, demandas)
        ]
        recomendacao, plano_recomendado = recomendar_barras_adicionais(
            diametro,
            faltas,
            barra_padrao_recomendacao,
            kerf,
            limite_retalho,
            desperdicio_max_recomendado,
        )

        barras_acima_desperdicio_recomendado = sum(
            int(linha.get("QTD_BARRAS", 0))
            for linha in plano_recomendado
            if float(linha.get("SOBRA_POR_BARRA_MM", 0.0)) < limite_retalho
            and float(linha.get("SOBRA_POR_BARRA_MM", 0.0)) > desperdicio_max_recomendado
        )
        maior_desperdicio_por_barra = max(
            (
                float(linha.get("SOBRA_POR_BARRA_MM", 0.0))
                for linha in plano_recomendado
                if float(linha.get("SOBRA_POR_BARRA_MM", 0.0)) < limite_retalho
            ),
            default=0.0,
        )

        resumo = {
            "DIAMETRO": diametro,
            "DEMANDA_TOTAL_PECAS": int(sum(demandas)),
            "DEMANDA_TOTAL_MM": round(sum(c * d for c, d in zip(comprimentos, demandas)), 2),
            "DEMANDA_ATENDIDA_MM": 0.0,
            "PECAS_ATENDIDAS": 0,
            "PECAS_FALTANTES": int(sum(demandas)),
            "ATENDIMENTO_PERCENTUAL": 0.0,
            "BARRAS_NOVAS_USADAS": 0,
            "RETALHOS_USADOS": 0,
            "TOTAL_FONTES_USADAS": 0,
            "SOBRA_FISICA_TOTAL_MM": 0.0,
            "DESPERDICIO_REAL_MM": 0.0,
            "DESPERDICIO_MAX_RECOMENDADO_MM": round(desperdicio_max_recomendado, 2),
            "BARRAS_ACIMA_DESPERDICIO_RECOMENDADO": barras_acima_desperdicio_recomendado,
            "MAIOR_DESPERDICIO_POR_BARRA_MM": round(maior_desperdicio_por_barra, 2),
            "RETALHO_REAPROVEITAVEL_BARRAS": 0,
            "RETALHO_REAPROVEITAVEL_MM": 0.0,
            "APROVEITAMENTO_PERCENTUAL": 0.0,
            "BARRAS_ADICIONAIS_RECOMENDADAS": (
                int(recomendacao[0]["BARRAS_PADRAO_RECOMENDADAS"])
                if recomendacao and isinstance(recomendacao[0].get("BARRAS_PADRAO_RECOMENDADAS"), (int, float))
                else 0
            ),
            "ATENDIMENTO_FINAL_PERCENTUAL": 100.0 if plano_recomendado else 0.0,
            "STATUS": (
                "Estoque sem padrao viavel; plano com barras padrao recomendado"
                if plano_recomendado
                else "Estoque sem padrao viavel para esta demanda"
            ),
        }
        return plano_recomendado, resumo, faltas, recomendacao

    # ---------------------------------------------------------
    # ORCAMENTO TOTAL DE OTIMIZACAO: 60 segundos por diametro
    # ---------------------------------------------------------
    inicio_otimizacao = time.monotonic()

    # -----------------------------------------------------------------
    # ETAPA E1: minimizar faltas; em empate, minimizar mm faltantes
    # -----------------------------------------------------------------
    solver1 = criar_solver()

    x1 = {}
    for s, classe in enumerate(classes):
        for j in range(len(padroes_por_classe[s])):
            x1[(s, j)] = solver1.IntVar(
                0,
                classe["quantidade"],
                f"xe1_{s}_{j}",
            )

        solver1.Add(
            solver1.Sum(
                x1[(s, j)]
                for j in range(len(padroes_por_classe[s]))
            )
            <= classe["quantidade"]
        )

    faltas1 = [
        solver1.IntVar(0, demandas[i], f"falta1_{i}")
        for i in range(len(comprimentos))
    ]

    for i, demanda in enumerate(demandas):
        producao = solver1.Sum(
            padroes_por_classe[s][j]["padrao"][i] * x1[(s, j)]
            for s in range(len(classes))
            for j in range(len(padroes_por_classe[s]))
        )
        solver1.Add(producao + faltas1[i] == demanda)

    # BIG_M garante prioridade ao numero de pecas faltantes.
    escala = 1000
    comprimentos_int = [
        int(round(c * escala))
        for c in comprimentos
    ]
    total_comp_demanda_int = sum(
        c * d
        for c, d in zip(comprimentos_int, demandas)
    )
    big_m = total_comp_demanda_int + 1

    solver1.Minimize(
        solver1.Sum(
            (big_m + comprimentos_int[i]) * faltas1[i]
            for i in range(len(comprimentos))
        )
    )

    solver1.SetTimeLimit(
        max(1, tempo_restante_otimizacao_ms(inicio_otimizacao))
    )
    status1 = solver1.Solve()

    if status1 not in (
        pywraplp.Solver.OPTIMAL,
        pywraplp.Solver.FEASIBLE,
    ):
        raise RuntimeError(
            f"Diametro {diametro}: nenhuma solucao viavel foi encontrada "
            "dentro do limite de 60 segundos."
        )

    melhor_faltas_unidades = int(
        round(sum(v.solution_value() for v in faltas1))
    )
    melhor_faltas_comp_int = sum(
        comprimentos_int[i]
        * int(round(faltas1[i].solution_value()))
        for i in range(len(comprimentos))
    )

    # Se E1 nao conseguiu provar o melhor atendimento dentro do tempo,
    # mantemos a melhor solucao viavel encontrada.
    if status1 != pywraplp.Solver.OPTIMAL:
        usar_x = x1
        usar_faltas = faltas1
        status_texto = (
            "Melhor atendimento viavel encontrado em ate 60 segundos; "
            "otimo global nao comprovado"
        )

    elif tempo_restante_otimizacao_ms(inicio_otimizacao) <= 0:
        usar_x = x1
        usar_faltas = faltas1
        status_texto = (
            "Melhor atendimento comprovado; limite total de 60 segundos "
            "atingido antes do refinamento"
        )

    else:
        # -----------------------------------------------------------------
        # ETAPA E2: mantendo o melhor atendimento, minimizar comprimento
        # total retirado do estoque.
        # -----------------------------------------------------------------
        solver2 = criar_solver()
        x2 = {}

        for s, classe in enumerate(classes):
            for j in range(len(padroes_por_classe[s])):
                x2[(s, j)] = solver2.IntVar(
                    0,
                    classe["quantidade"],
                    f"xe2_{s}_{j}",
                )

            solver2.Add(
                solver2.Sum(
                    x2[(s, j)]
                    for j in range(len(padroes_por_classe[s]))
                )
                <= classe["quantidade"]
            )

        faltas2 = [
            solver2.IntVar(0, demandas[i], f"falta2_{i}")
            for i in range(len(comprimentos))
        ]

        for i, demanda in enumerate(demandas):
            producao = solver2.Sum(
                padroes_por_classe[s][j]["padrao"][i] * x2[(s, j)]
                for s in range(len(classes))
                for j in range(len(padroes_por_classe[s]))
            )
            solver2.Add(producao + faltas2[i] == demanda)

        solver2.Add(
            solver2.Sum(faltas2)
            == melhor_faltas_unidades
        )
        solver2.Add(
            solver2.Sum(
                comprimentos_int[i] * faltas2[i]
                for i in range(len(comprimentos))
            )
            == melhor_faltas_comp_int
        )

        # -------------------------------------------------------------
        # POLÍTICA EMERGENCIAL V3.2
        # -------------------------------------------------------------
        # Mantendo o melhor atendimento encontrado na Etapa E1, a solução
        # passa a priorizar, nesta ordem prática:
        #   1) bons padrões em RETALHOS existentes;
        #   2) BARRAS NOVAS já existentes no estoque;
        #   3) padrões de retalho com desperdício acima do recomendado.
        #
        # Isso evita abandonar casos que podem ser resolvidos de forma
        # melhor ao liberar barras novas do estoque, sem deixar de dar
        # preferência ao reaproveitamento de bons retalhos.
        comprimento_total_estoque = sum(
            float(c["comprimento"]) * int(c["quantidade"])
            for c in classes
        )
        penalidade_nova = max(1.0, comprimento_total_estoque + 1.0)
        penalidade_retalho_ruim = penalidade_nova * 2.0

        solver2.Minimize(
            solver2.Sum(
                (
                    classes[s]["comprimento"]
                    + padroes_por_classe[s][j]["excesso_recomendado"]
                    + (
                        penalidade_nova
                        if classes[s]["tipo"] == "NOVA"
                        else 0.0
                    )
                    + (
                        penalidade_retalho_ruim
                        if (
                            classes[s]["tipo"] == "RETALHO"
                            and not padroes_por_classe[s][j]["padrao_preferencial"]
                        )
                        else 0.0
                    )
                )
                * x2[(s, j)]
                for s in range(len(classes))
                for j in range(len(padroes_por_classe[s]))
            )
        )

        tempo_restante = tempo_restante_otimizacao_ms(
            inicio_otimizacao
        )

        if tempo_restante <= 0:
            usar_x = x1
            usar_faltas = faltas1
            status_texto = (
                "Melhor atendimento comprovado; limite total de 60 segundos "
                "atingido antes da Etapa E2"
            )
        else:
            solver2.SetTimeLimit(tempo_restante)
            status2 = solver2.Solve()

            if status2 not in (
                pywraplp.Solver.OPTIMAL,
                pywraplp.Solver.FEASIBLE,
            ):
                usar_x = x1
                usar_faltas = faltas1
                status_texto = (
                    "Melhor atendimento comprovado; solucao da Etapa E1 "
                    "mantida ao atingir o limite de 60 segundos"
                )
            else:
                usar_x = x2
                usar_faltas = faltas2
                status_texto = (
                    "Otima comprovada dentro do limite total de 60 segundos"
                    if status2 == pywraplp.Solver.OPTIMAL
                    else "Melhor solucao viavel encontrada dentro do limite total de 60 segundos"
                )

    linhas_plano = []
    total_desperdicio = 0.0
    total_retalho = 0.0
    total_sobra = 0.0
    novas_usadas = 0
    retalhos_usados = 0
    total_fontes = 0
    id_padrao = 1

    for s, classe in enumerate(classes):
        for j, reg in enumerate(padroes_por_classe[s]):
            vezes = int(round(usar_x[(s, j)].solution_value()))
            if vezes <= 0:
                continue

            total_fontes += vezes
            if classe["tipo"] == "NOVA":
                novas_usadas += vezes
            else:
                retalhos_usados += vezes

            sobra = reg["sobra"]
            total_sobra += sobra * vezes

            if sobra >= limite_retalho:
                total_retalho += sobra * vezes
                classificacao = "RETALHO REAPROVEITAVEL"
            else:
                total_desperdicio += sobra * vezes
                classificacao = "DESPERDICIO"

            partes = []
            for qtd, comp in zip(reg["padrao"], comprimentos):
                if qtd > 0:
                    partes.append(f"{qtd}x({comp:g}mm)")

            linhas_plano.append(
                {
                    "MODO": "EMERGENCIAL",
                    "DIAMETRO": diametro,
                    "ID_PADRAO": f"E{diametro:g}-{id_padrao}",
                    "TIPO_FONTE": classe["tipo"],
                    "COMPRIMENTO_FONTE_MM": classe["comprimento"],
                    "QTD_BARRAS": vezes,
                    "ESQUEMA_DE_CORTE": " + ".join(partes),
                    "SOBRA_POR_BARRA_MM": sobra,
                    "CLASSIFICACAO_SOBRA": classificacao,
                    "ORIGEM_PLANO": "ESTOQUE_ATUAL",
                }
            )
            id_padrao += 1

    faltas = []
    total_faltante = 0
    for i, comp in enumerate(comprimentos):
        qtd_falta = int(round(usar_faltas[i].solution_value()))
        if qtd_falta > 0:
            faltas.append(
                {
                    "DIAMETRO": diametro,
                    "COMPRIMENTO": comp,
                    "QTD_FALTANTE": qtd_falta,
                }
            )
            total_faltante += qtd_falta

    demanda_total = int(sum(demandas))
    atendidas = demanda_total - total_faltante
    percentual = 100.0 * atendidas / demanda_total if demanda_total else 100.0

    demanda_total_mm = sum(c * d for c, d in zip(comprimentos, demandas))
    faltante_total_mm = sum(
        f["COMPRIMENTO"] * f["QTD_FALTANTE"] for f in faltas
    )
    demanda_atendida_mm = demanda_total_mm - faltante_total_mm

    material_total_usado_mm = 0.0
    retalhos_gerados_barras = 0
    for s, classe in enumerate(classes):
        for j, reg in enumerate(padroes_por_classe[s]):
            vezes = int(round(usar_x[(s, j)].solution_value()))
            if vezes <= 0:
                continue
            material_total_usado_mm += classe["comprimento"] * vezes
            if reg["sobra"] >= limite_retalho:
                retalhos_gerados_barras += vezes

    aproveitamento_percentual = (
        100.0 * demanda_atendida_mm / material_total_usado_mm
        if material_total_usado_mm > 0
        else 0.0
    )

    recomendacao, plano_recomendado = recomendar_barras_adicionais(
        diametro,
        faltas,
        barra_padrao_recomendacao,
        kerf,
        limite_retalho,
        desperdicio_max_recomendado,
    )

    plano_final_avaliacao = linhas_plano + plano_recomendado
    barras_acima_desperdicio_recomendado = sum(
        int(linha.get("QTD_BARRAS", 0))
        for linha in plano_final_avaliacao
        if float(linha.get("SOBRA_POR_BARRA_MM", 0.0)) < limite_retalho
        and float(linha.get("SOBRA_POR_BARRA_MM", 0.0)) > desperdicio_max_recomendado
    )
    maior_desperdicio_por_barra = max(
        (
            float(linha.get("SOBRA_POR_BARRA_MM", 0.0))
            for linha in plano_final_avaliacao
            if float(linha.get("SOBRA_POR_BARRA_MM", 0.0)) < limite_retalho
        ),
        default=0.0,
    )

    resumo = {
        "DIAMETRO": diametro,
        "DEMANDA_TOTAL_PECAS": demanda_total,
        "DEMANDA_TOTAL_MM": round(demanda_total_mm, 2),
        "DEMANDA_ATENDIDA_MM": round(demanda_atendida_mm, 2),
        "PECAS_ATENDIDAS": atendidas,
        "PECAS_FALTANTES": total_faltante,
        "ATENDIMENTO_PERCENTUAL": round(percentual, 2),
        "BARRAS_NOVAS_USADAS": novas_usadas,
        "RETALHOS_USADOS": retalhos_usados,
        "TOTAL_FONTES_USADAS": total_fontes,
        "SOBRA_FISICA_TOTAL_MM": round(total_sobra, 2),
        "DESPERDICIO_REAL_MM": round(total_desperdicio, 2),
        "DESPERDICIO_MAX_RECOMENDADO_MM": round(desperdicio_max_recomendado, 2),
        "BARRAS_ACIMA_DESPERDICIO_RECOMENDADO": barras_acima_desperdicio_recomendado,
        "MAIOR_DESPERDICIO_POR_BARRA_MM": round(maior_desperdicio_por_barra, 2),
        "RETALHO_REAPROVEITAVEL_BARRAS": retalhos_gerados_barras,
        "RETALHO_REAPROVEITAVEL_MM": round(total_retalho, 2),
        "APROVEITAMENTO_PERCENTUAL": round(aproveitamento_percentual, 2),
        "BARRAS_ADICIONAIS_RECOMENDADAS": (
            int(recomendacao[0]["BARRAS_PADRAO_RECOMENDADAS"])
            if recomendacao and isinstance(recomendacao[0].get("BARRAS_PADRAO_RECOMENDADAS"), (int, float))
            else 0
        ),
        "ATENDIMENTO_FINAL_PERCENTUAL": (
            100.0 if (not faltas or plano_recomendado) else round(percentual, 2)
        ),
        "STATUS": (
            status_texto + " | Plano adicional com barras padrao gerado para completar a demanda"
            if faltas and plano_recomendado
            else status_texto
        ),
    }

    # O plano final emergencial deve ser executavel: quando houver falta,
    # incorpora automaticamente o corte recomendado em barras padrao.
    linhas_plano.extend(plano_recomendado)

    return linhas_plano, resumo, faltas, recomendacao


def recomendar_barras_adicionais(
    diametro,
    faltas,
    tamanho_barra,
    kerf,
    limite_retalho,
    desperdicio_max_recomendado,
):
    """
    Gera o complemento necessario para atender as pecas faltantes usando
    barras padrao. Alem da quantidade de barras, devolve o plano de corte
    otimizado que deve ser incorporado ao plano emergencial.
    """
    if not faltas:
        return [], []

    df = pd.DataFrame(
        [
            {
                "DIAMETRO": diametro,
                "COMPRIMENTO": f["COMPRIMENTO"],
                "DEMANDA": f["QTD_FALTANTE"],
            }
            for f in faltas
        ]
    )

    try:
        plano, resumo = otimizar_planejado_por_diametro(
            diametro,
            df,
            tamanho_barra,
            kerf,
            limite_retalho,
            desperdicio_max_recomendado,
        )

        plano_recomendado = []
        for indice, linha in enumerate(plano, start=1):
            nova_linha = dict(linha)
            nova_linha["MODO"] = "EMERGENCIAL"
            nova_linha["ID_PADRAO"] = f"R{diametro:g}-{indice}"
            nova_linha["TIPO_FONTE"] = "BARRA_PADRAO_RECOMENDADA"
            nova_linha["ORIGEM_PLANO"] = "COMPLEMENTO_PARA_ATENDER_DEMANDA"
            plano_recomendado.append(nova_linha)

        recomendacao = [
            {
                "DIAMETRO": diametro,
                "BARRAS_PADRAO_RECOMENDADAS": resumo["BARRAS_NOVAS_USADAS"],
                "COMPRIMENTO_BARRA_MM": tamanho_barra,
                "ATENDIMENTO_FINAL_PERCENTUAL": 100.0,
                "OBSERVACAO": (
                    "Usar barras padrao do estoque/reserva conforme o plano de corte "
                    "recomendado para completar as pecas faltantes."
                ),
            }
        ]

        return recomendacao, plano_recomendado

    except Exception as erro:
        return (
            [
                {
                    "DIAMETRO": diametro,
                    "BARRAS_PADRAO_RECOMENDADAS": "NAO CALCULADO",
                    "COMPRIMENTO_BARRA_MM": tamanho_barra,
                    "ATENDIMENTO_FINAL_PERCENTUAL": 0.0,
                    "OBSERVACAO": str(erro),
                }
            ],
            [],
        )

def executar_emergencial(
    df_demanda,
    df_estoque,
    kerf,
    limite_retalho,
    desperdicio_max_recomendado,
    barra_padrao_recomendacao,
):
    plano_total = []
    resumos = []
    faltas_total = []
    recomendacoes_total = []

    for diametro in sorted(df_demanda["DIAMETRO"].unique()):
        demanda_d = df_demanda[df_demanda["DIAMETRO"] == diametro].copy()
        estoque_d = df_estoque[df_estoque["DIAMETRO"] == diametro].copy()

        linhas, resumo, faltas, recomendacoes = otimizar_emergencial_por_diametro(
            diametro,
            demanda_d,
            estoque_d,
            kerf,
            limite_retalho,
            desperdicio_max_recomendado,
            barra_padrao_recomendacao,
        )

        plano_total.extend(linhas)
        resumos.append(resumo)
        faltas_total.extend(faltas)
        recomendacoes_total.extend(recomendacoes)

    return (
        pd.DataFrame(plano_total),
        pd.DataFrame(resumos),
        pd.DataFrame(faltas_total),
        pd.DataFrame(recomendacoes_total),
    )


# =====================================================================
# EXPORTACAO EXCEL
# =====================================================================

def exportar_excel_planejado(caminho_demanda, plano, resumo, demanda):
    pasta = os.path.dirname(caminho_demanda)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    caminho = os.path.join(pasta, f"Plano_Corte_Planejado_{timestamp}.xlsx")

    with pd.ExcelWriter(caminho) as writer:
        resumo.to_excel(writer, sheet_name="RESUMO", index=False)
        plano.to_excel(writer, sheet_name="PLANO_DE_CORTE", index=False)
        demanda.to_excel(writer, sheet_name="DEMANDA", index=False)

    return caminho


def exportar_excel_emergencial(
    caminho_demanda,
    plano,
    resumo,
    faltas,
    recomendacoes,
    demanda,
    estoque,
):
    pasta = os.path.dirname(caminho_demanda)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    caminho = os.path.join(pasta, f"Plano_Corte_Emergencial_{timestamp}.xlsx")

    # A primeira aba e o documento operacional: combina o que sera cortado
    # do estoque informado com as barras padrao recomendadas para completar
    # a demanda, caso o estoque inicial seja insuficiente.
    plano_completo = plano.copy()
    if not plano_completo.empty and "ORIGEM_PLANO" not in plano_completo.columns:
        plano_completo["ORIGEM_PLANO"] = "ESTOQUE_ATUAL"

    if not plano_completo.empty:
        plano_estoque = plano_completo[
            plano_completo["ORIGEM_PLANO"] == "ESTOQUE_ATUAL"
        ].copy()
        plano_complemento = plano_completo[
            plano_completo["ORIGEM_PLANO"] == "COMPLEMENTO_PARA_ATENDER_DEMANDA"
        ].copy()
    else:
        plano_estoque = pd.DataFrame()
        plano_complemento = pd.DataFrame()

    # Exportacao operacional do modo emergencial:
    # mantem apenas as abas necessarias para o operador executar o corte.
    with pd.ExcelWriter(caminho) as writer:
        plano_completo.to_excel(writer, sheet_name="PLANO_COMPLETO", index=False)

        if plano_estoque.empty:
            pd.DataFrame(
                [{"STATUS": "NENHUM CORTE POSSIVEL COM O ESTOQUE INFORMADO"}]
            ).to_excel(
                writer, sheet_name="CORTE_ESTOQUE", index=False
            )
        else:
            plano_estoque.to_excel(writer, sheet_name="CORTE_ESTOQUE", index=False)

        if plano_complemento.empty:
            pd.DataFrame(
                [{"STATUS": "NAO FOI NECESSARIO COMPLEMENTO COM BARRA PADRAO"}]
            ).to_excel(
                writer, sheet_name="CORTE_COMPLEMENTO", index=False
            )
        else:
            plano_complemento.to_excel(
                writer, sheet_name="CORTE_COMPLEMENTO", index=False
            )

    return caminho


# =====================================================================
# INTERFACE GRAFICA
# =====================================================================

class PrincipiaMinimaApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Principia Minima - Otimizacao de Corte")
        self.state("zoomed")

        self.caminho_demanda_planejado = None
        self.caminho_demanda_emergencial = None
        self.caminho_estoque_emergencial = None

        self._configurar_estilo()
        self.mostrar_inicio()

    def _configurar_estilo(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Titulo.TLabel", font=("Arial", 22, "bold"))
        style.configure("Subtitulo.TLabel", font=("Arial", 11))
        style.configure("Acao.TButton", font=("Arial", 11, "bold"), padding=10)

    def limpar(self):
        for widget in self.winfo_children():
            widget.destroy()

    # -----------------------------------------------------------------
    # INICIO
    # -----------------------------------------------------------------
    def mostrar_inicio(self):
        self.limpar()

        frame = ttk.Frame(self, padding=40)
        frame.pack(expand=True, fill="both")

        ttk.Label(frame, text="PRINCIPIA MINIMA", style="Titulo.TLabel").pack(pady=(35, 5))
        ttk.Label(
            frame,
            text="Sistema de Otimizacao de Corte de Barras de Cobre",
            style="Subtitulo.TLabel",
        ).pack(pady=(0, 35))

        cards = ttk.Frame(frame)
        cards.pack(expand=True)

        emerg = ttk.LabelFrame(cards, text="EMERGENCIAL", padding=25)
        emerg.grid(row=0, column=0, padx=15, pady=10, sticky="nsew")
        ttk.Label(
            emerg,
            text="Estoque atual + demanda semanal\n\nUsa barras novas e retalhos disponiveis.",
            justify="center",
        ).pack(pady=10)
        ttk.Button(
            emerg,
            text="ABRIR MODO EMERGENCIAL",
            style="Acao.TButton",
            command=self.mostrar_emergencial,
        ).pack(pady=12)

        planej = ttk.LabelFrame(cards, text="PLANEJADO", padding=25)
        planej.grid(row=0, column=1, padx=15, pady=10, sticky="nsew")
        ttk.Label(
            planej,
            text="Barras padrao + demanda futura\n\nCalcula a necessidade planejada de material.",
            justify="center",
        ).pack(pady=10)
        ttk.Button(
            planej,
            text="ABRIR MODO PLANEJADO",
            style="Acao.TButton",
            command=self.mostrar_planejado,
        ).pack(pady=12)

        ttk.Label(
            frame,
            text="Versao 2.0 - Planejamento semanal por multiplos diametros",
            foreground="gray",
        ).pack(side="bottom", pady=10)

    # -----------------------------------------------------------------
    # PLANEJADO
    # -----------------------------------------------------------------
    def mostrar_planejado(self):
        self.limpar()
        self.caminho_demanda_planejado = None

        frame = ttk.Frame(self, padding=25)
        frame.pack(fill="both", expand=True)

        ttk.Button(frame, text="< Voltar", command=self.mostrar_inicio).pack(anchor="w")
        ttk.Label(frame, text="PLANEJAMENTO FUTURO", style="Titulo.TLabel").pack(pady=(15, 5))
        ttk.Label(
            frame,
            text="Carregue uma unica planilha com todos os diametros da demanda futura.",
        ).pack(pady=(0, 20))

        entrada = ttk.LabelFrame(frame, text="Parametros", padding=15)
        entrada.pack(fill="x", pady=10)

        ttk.Label(entrada, text="Barra padrao (mm)").grid(row=0, column=0, padx=8, pady=4)
        self.entry_barra_p = ttk.Entry(entrada, width=15)
        self.entry_barra_p.insert(0, str(BARRA_PADRAO_DEFAULT))
        self.entry_barra_p.grid(row=1, column=0, padx=8)

        ttk.Label(entrada, text="Kerf (mm)").grid(row=0, column=1, padx=8, pady=4)
        self.entry_kerf_p = ttk.Entry(entrada, width=15)
        self.entry_kerf_p.insert(0, str(KERF_DEFAULT))
        self.entry_kerf_p.grid(row=1, column=1, padx=8)

        ttk.Label(entrada, text="Limite retalho (mm)").grid(row=0, column=2, padx=8, pady=4)
        self.entry_retalho_p = ttk.Entry(entrada, width=15)
        self.entry_retalho_p.insert(0, str(LIMITE_RETALHO_DEFAULT))
        self.entry_retalho_p.grid(row=1, column=2, padx=8)

        ttk.Label(entrada, text="Desperdicio max. recomendado (mm)").grid(
            row=0, column=3, padx=8, pady=4
        )
        self.entry_desperdicio_max_p = ttk.Entry(entrada, width=22)
        self.entry_desperdicio_max_p.insert(
            0, str(DESPERDICIO_MAX_RECOMENDADO_DEFAULT)
        )
        self.entry_desperdicio_max_p.grid(row=1, column=3, padx=8)

        arquivos = ttk.LabelFrame(frame, text="Demanda", padding=15)
        arquivos.pack(fill="x", pady=10)

        ttk.Button(
            arquivos,
            text="Selecionar planilha de demanda (.csv)",
            command=self.selecionar_demanda_planejado,
        ).pack(anchor="w")

        self.label_demanda_p = ttk.Label(arquivos, text="Nenhum arquivo selecionado.")
        self.label_demanda_p.pack(anchor="w", pady=(8, 0))

        ttk.Label(
            arquivos,
            text="Formato preferencial: PIV;LINHA;DIAMETRO;COMPRIMENTO;DEMANDA",
            foreground="gray",
        ).pack(anchor="w", pady=(4, 0))

        ttk.Button(
            frame,
            text="OTIMIZAR E GERAR EXCEL",
            style="Acao.TButton",
            command=self.processar_planejado,
        ).pack(pady=30)

    def selecionar_demanda_planejado(self):
        caminho = filedialog.askopenfilename(
            title="Selecione a demanda futura",
            filetypes=[("Arquivos CSV", "*.csv")],
        )
        if caminho:
            self.caminho_demanda_planejado = caminho
            self.label_demanda_p.config(text=os.path.basename(caminho))

    def processar_planejado(self):
        if not self.caminho_demanda_planejado:
            messagebox.showwarning("Demanda", "Selecione a planilha de demanda.")
            return

        try:
            tamanho_barra = float(self.entry_barra_p.get().replace(",", "."))
            kerf = float(self.entry_kerf_p.get().replace(",", "."))
            limite = float(self.entry_retalho_p.get().replace(",", "."))
            desperdicio_max = float(
                self.entry_desperdicio_max_p.get().replace(",", ".")
            )

            if (
                min(tamanho_barra, kerf, limite, desperdicio_max) < 0
                or tamanho_barra <= 0
            ):
                raise ValueError("Parametros fisicos invalidos.")

            df_demanda_detalhada = ler_demanda_csv(self.caminho_demanda_planejado)
            df_demanda = agrupar_demanda_para_solver(df_demanda_detalhada)

            plano, resumo = executar_planejado(
                df_demanda,
                tamanho_barra,
                kerf,
                limite,
                desperdicio_max,
            )
            plano = adicionar_rastreabilidade_ao_plano(
                plano,
                df_demanda_detalhada,
            )

            caminho_excel = exportar_excel_planejado(
                self.caminho_demanda_planejado,
                plano,
                resumo,
                df_demanda_detalhada.drop(columns=["_ORDEM"], errors="ignore"),
            )

            self.mostrar_resultado(
                "PLANEJADO",
                resumo,
                caminho_excel,
                pd.DataFrame(),
            )

        except Exception as erro:
            messagebox.showerror("Erro de Processamento", str(erro))

    # -----------------------------------------------------------------
    # EMERGENCIAL
    # -----------------------------------------------------------------
    def mostrar_emergencial(self):
        self.limpar()
        self.caminho_demanda_emergencial = None
        self.caminho_estoque_emergencial = None

        frame = ttk.Frame(self, padding=25)
        frame.pack(fill="both", expand=True)

        ttk.Button(frame, text="< Voltar", command=self.mostrar_inicio).pack(anchor="w")
        ttk.Label(frame, text="PLANEJAMENTO EMERGENCIAL", style="Titulo.TLabel").pack(pady=(10, 5))
        ttk.Label(
            frame,
            text=(
                "Carregue a demanda semanal e informe o estoque manualmente "
                "e/ou por planilha."
            ),
        ).pack(pady=(0, 12))

        entrada = ttk.LabelFrame(frame, text="Parametros", padding=12)
        entrada.pack(fill="x", pady=6)

        ttk.Label(entrada, text="Kerf (mm)").grid(row=0, column=0, padx=8, pady=4)
        self.entry_kerf_e = ttk.Entry(entrada, width=15)
        self.entry_kerf_e.insert(0, str(KERF_DEFAULT))
        self.entry_kerf_e.grid(row=1, column=0, padx=8)

        ttk.Label(entrada, text="Limite retalho (mm)").grid(row=0, column=1, padx=8, pady=4)
        self.entry_retalho_e = ttk.Entry(entrada, width=15)
        self.entry_retalho_e.insert(0, str(LIMITE_RETALHO_DEFAULT))
        self.entry_retalho_e.grid(row=1, column=1, padx=8)

        ttk.Label(entrada, text="Barra padrao (mm)").grid(
            row=0, column=2, padx=8, pady=4
        )
        self.entry_barra_e = ttk.Entry(entrada, width=18)
        self.entry_barra_e.insert(0, str(BARRA_PADRAO_DEFAULT))
        self.entry_barra_e.grid(row=1, column=2, padx=8)

        ttk.Label(entrada, text="Desperdicio max. recomendado (mm)").grid(
            row=0, column=3, padx=8, pady=4
        )
        self.entry_desperdicio_max_e = ttk.Entry(entrada, width=22)
        self.entry_desperdicio_max_e.insert(
            0, str(DESPERDICIO_MAX_RECOMENDADO_DEFAULT)
        )
        self.entry_desperdicio_max_e.grid(row=1, column=3, padx=8)

        demanda_box = ttk.LabelFrame(frame, text="Demanda semanal", padding=12)
        demanda_box.pack(fill="x", pady=6)

        ttk.Button(
            demanda_box,
            text="Selecionar demanda semanal (.csv)",
            command=self.selecionar_demanda_emergencial,
        ).grid(row=0, column=0, padx=5, pady=5, sticky="w")
        self.label_demanda_e = ttk.Label(demanda_box, text="Nenhum arquivo selecionado.")
        self.label_demanda_e.grid(row=0, column=1, padx=10, sticky="w")
        ttk.Label(
            demanda_box,
            text="Formato preferencial: PIV;LINHA;DIAMETRO;COMPRIMENTO;DEMANDA",
            foreground="gray",
        ).grid(row=1, column=0, columnspan=2, sticky="w", padx=5)

        estoque_box = ttk.LabelFrame(frame, text="Estoque atual - manual e/ou planilha", padding=12)
        estoque_box.pack(fill="both", expand=True, pady=6)

        arquivo_estoque = ttk.Frame(estoque_box)
        arquivo_estoque.pack(fill="x", pady=(0, 10))

        ttk.Button(
            arquivo_estoque,
            text="Selecionar estoque (.csv)",
            command=self.selecionar_estoque_emergencial,
        ).grid(row=0, column=0, padx=5, pady=4, sticky="w")

        self.label_estoque_e = ttk.Label(
            arquivo_estoque,
            text="Nenhum arquivo de estoque selecionado.",
        )
        self.label_estoque_e.grid(row=0, column=1, padx=10, sticky="w")

        ttk.Label(
            arquivo_estoque,
            text="Formato: DIAMETRO;COMPRIMENTO;QUANTIDADE",
            foreground="gray",
        ).grid(row=1, column=0, columnspan=2, padx=5, sticky="w")

        ttk.Label(
            arquivo_estoque,
            text="Os dados da planilha e os itens inseridos manualmente serao somados.",
            foreground="gray",
        ).grid(row=2, column=0, columnspan=2, padx=5, sticky="w")

        formulario = ttk.Frame(estoque_box)
        formulario.pack(fill="x", pady=(0, 8))

        ttk.Label(formulario, text="Diametro").grid(row=0, column=0, padx=5)
        self.entry_diametro_estoque_e = ttk.Entry(formulario, width=14)
        self.entry_diametro_estoque_e.grid(row=1, column=0, padx=5)

        ttk.Label(formulario, text="Comprimento (mm)").grid(row=0, column=1, padx=5)
        self.entry_comprimento_estoque_e = ttk.Entry(formulario, width=16)
        self.entry_comprimento_estoque_e.grid(row=1, column=1, padx=5)

        ttk.Label(formulario, text="Quantidade").grid(row=0, column=2, padx=5)
        self.entry_quantidade_estoque_e = ttk.Entry(formulario, width=12)
        self.entry_quantidade_estoque_e.grid(row=1, column=2, padx=5)

        ttk.Button(
            formulario,
            text="Adicionar",
            command=self.adicionar_estoque_emergencial,
        ).grid(row=1, column=3, padx=8)

        ttk.Button(
            formulario,
            text="Remover selecionado",
            command=self.remover_estoque_emergencial,
        ).grid(row=1, column=4, padx=5)

        self.tabela_estoque_e = ttk.Treeview(
            estoque_box,
            columns=("diametro", "comprimento", "quantidade"),
            show="headings",
            height=6,
        )
        self.tabela_estoque_e.heading("diametro", text="Diametro")
        self.tabela_estoque_e.heading("comprimento", text="Comprimento (mm)")
        self.tabela_estoque_e.heading("quantidade", text="Quantidade")
        self.tabela_estoque_e.column("diametro", anchor="center", width=140)
        self.tabela_estoque_e.column("comprimento", anchor="center", width=190)
        self.tabela_estoque_e.column("quantidade", anchor="center", width=140)
        self.tabela_estoque_e.pack(fill="both", expand=True)

        ttk.Label(
            estoque_box,
            text=(
                "Informe barras completas e retalhos manualmente ou carregue uma planilha. "
                "O sistema identifica como barra nova o item cujo comprimento for igual "
                "a barra padrao."
            ),
            foreground="gray",
        ).pack(anchor="w", pady=(6, 0))

        ttk.Button(
            frame,
            text="OTIMIZAR SEMANA E GERAR EXCEL",
            style="Acao.TButton",
            command=self.processar_emergencial,
        ).pack(pady=12)

    def selecionar_demanda_emergencial(self):
        caminho = filedialog.askopenfilename(
            title="Selecione a demanda semanal",
            filetypes=[("Arquivos CSV", "*.csv")],
        )
        if caminho:
            self.caminho_demanda_emergencial = caminho
            self.label_demanda_e.config(text=os.path.basename(caminho))

    def selecionar_estoque_emergencial(self):
        caminho = filedialog.askopenfilename(
            title="Selecione a planilha de estoque atual",
            filetypes=[("Arquivos CSV", "*.csv")],
        )
        if caminho:
            self.caminho_estoque_emergencial = caminho
            self.label_estoque_e.config(text=os.path.basename(caminho))

    def adicionar_estoque_emergencial(self):
        try:
            diametro = float(self.entry_diametro_estoque_e.get().replace(",", "."))
            comprimento = float(self.entry_comprimento_estoque_e.get().replace(",", "."))
            quantidade_float = float(self.entry_quantidade_estoque_e.get().replace(",", "."))

            if diametro <= 0 or comprimento <= 0 or quantidade_float <= 0:
                raise ValueError("Os valores devem ser maiores que zero.")
            if not quantidade_float.is_integer():
                raise ValueError("A quantidade deve ser um numero inteiro.")

            quantidade = int(quantidade_float)
            self.tabela_estoque_e.insert(
                "",
                "end",
                values=(f"{diametro:g}", f"{comprimento:g}", quantidade),
            )

            self.entry_diametro_estoque_e.delete(0, "end")
            self.entry_comprimento_estoque_e.delete(0, "end")
            self.entry_quantidade_estoque_e.delete(0, "end")
            self.entry_diametro_estoque_e.focus_set()

        except Exception as erro:
            messagebox.showerror("Estoque", f"Dados invalidos.\n\n{erro}")

    def remover_estoque_emergencial(self):
        selecionados = self.tabela_estoque_e.selection()
        if not selecionados:
            messagebox.showwarning("Estoque", "Selecione uma linha para remover.")
            return
        for item in selecionados:
            self.tabela_estoque_e.delete(item)

    def obter_estoque_emergencial(self, barra_padrao):
        dataframes = []

        # 1) Estoque carregado por planilha
        if self.caminho_estoque_emergencial:
            dataframes.append(
                ler_estoque_csv(
                    self.caminho_estoque_emergencial,
                    barra_padrao,
                )
            )

        # 2) Estoque informado manualmente
        registros_manuais = []

        for item in self.tabela_estoque_e.get_children():
            valores = self.tabela_estoque_e.item(item, "values")
            diametro = float(str(valores[0]).replace(",", "."))
            comprimento = float(str(valores[1]).replace(",", "."))
            quantidade = int(valores[2])

            tipo = (
                "NOVA"
                if abs(comprimento - barra_padrao) <= 1e-6
                else "RETALHO"
            )

            registros_manuais.append(
                {
                    "TIPO": tipo,
                    "DIAMETRO": round(diametro, 4),
                    "COMPRIMENTO": round(comprimento, 4),
                    "QUANTIDADE": quantidade,
                }
            )

        if registros_manuais:
            dataframes.append(pd.DataFrame(registros_manuais))

        if not dataframes:
            raise ValueError(
                "Informe pelo menos um item de estoque manualmente "
                "ou selecione uma planilha de estoque."
            )

        df = pd.concat(dataframes, ignore_index=True)

        return (
            df.groupby(
                ["TIPO", "DIAMETRO", "COMPRIMENTO"],
                as_index=False,
            )["QUANTIDADE"]
            .sum()
            .sort_values(
                ["DIAMETRO", "TIPO", "COMPRIMENTO"],
                ascending=[True, True, False],
            )
            .reset_index(drop=True)
        )

    def processar_emergencial(self):
        if not self.caminho_demanda_emergencial:
            messagebox.showwarning("Demanda", "Selecione a planilha de demanda semanal.")
            return

        try:
            kerf = float(self.entry_kerf_e.get().replace(",", "."))
            limite = float(self.entry_retalho_e.get().replace(",", "."))
            barra_padrao = float(self.entry_barra_e.get().replace(",", "."))
            desperdicio_max = float(
                self.entry_desperdicio_max_e.get().replace(",", ".")
            )

            if (
                kerf < 0
                or limite < 0
                or desperdicio_max < 0
                or barra_padrao <= 0
            ):
                raise ValueError("Parametros fisicos invalidos.")

            df_demanda_detalhada = ler_demanda_csv(
                self.caminho_demanda_emergencial
            )
            df_demanda = agrupar_demanda_para_solver(df_demanda_detalhada)
            df_estoque = self.obter_estoque_emergencial(barra_padrao)

            plano, resumo, faltas, recomendacoes = executar_emergencial(
                df_demanda,
                df_estoque,
                kerf,
                limite,
                desperdicio_max,
                barra_padrao,
            )

            plano = adicionar_rastreabilidade_ao_plano(
                plano,
                df_demanda_detalhada,
            )

            caminho_excel = exportar_excel_emergencial(
                self.caminho_demanda_emergencial,
                plano,
                resumo,
                faltas,
                recomendacoes,
                df_demanda_detalhada.drop(columns=["_ORDEM"], errors="ignore"),
                df_estoque,
            )

            self.mostrar_resultado(
                "EMERGENCIAL",
                resumo,
                caminho_excel,
                faltas,
            )

        except Exception as erro:
            messagebox.showerror("Erro de Processamento", str(erro))

    # -----------------------------------------------------------------
    # RESULTADO EM TELA
    # -----------------------------------------------------------------
    def mostrar_resultado(self, modo, resumo, caminho_excel, faltas):
        janela = tk.Toplevel(self)
        janela.title(f"Resultado - {modo}")
        janela.geometry("850x520")

        ttk.Label(
            janela,
            text=f"RESULTADO - {modo}",
            style="Titulo.TLabel",
        ).pack(pady=(20, 10))

        texto = tk.Text(janela, height=18, width=100, font=("Consolas", 10))
        texto.pack(fill="both", expand=True, padx=20, pady=10)

        for _, row in resumo.iterrows():
            texto.insert("end", f"DIAMETRO: {row['DIAMETRO']:g}\n")
            texto.insert("end", f"  Demanda total: {int(row['DEMANDA_TOTAL_PECAS'])} pecas\n")
            if "DEMANDA_TOTAL_MM" in resumo.columns:
                texto.insert("end", f"  Demanda total: {row['DEMANDA_TOTAL_MM']:.2f} mm\n")
            texto.insert("end", f"  Atendidas: {int(row['PECAS_ATENDIDAS'])}\n")
            texto.insert("end", f"  Faltantes: {int(row['PECAS_FALTANTES'])}\n")
            if "ATENDIMENTO_PERCENTUAL" in resumo.columns:
                texto.insert("end", f"  Atendimento com estoque informado: {row['ATENDIMENTO_PERCENTUAL']:.2f}%\n")
            if "BARRAS_ADICIONAIS_RECOMENDADAS" in resumo.columns and row["BARRAS_ADICIONAIS_RECOMENDADAS"] > 0:
                texto.insert(
                    "end",
                    f"  Barras padrao adicionais recomendadas: {int(row['BARRAS_ADICIONAIS_RECOMENDADAS'])}\n",
                )
            if "ATENDIMENTO_FINAL_PERCENTUAL" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Atendimento final com plano recomendado: {row['ATENDIMENTO_FINAL_PERCENTUAL']:.2f}%\n",
                )
            texto.insert("end", f"  Barras novas usadas: {int(row['BARRAS_NOVAS_USADAS'])}\n")
            texto.insert("end", f"  Retalhos usados: {int(row['RETALHOS_USADOS'])}\n")
            texto.insert("end", f"  Desperdicio real: {row['DESPERDICIO_REAL_MM']:.2f} mm\n")
            if "DESPERDICIO_MAX_RECOMENDADO_MM" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Desperdicio max. recomendado: "
                    f"{row['DESPERDICIO_MAX_RECOMENDADO_MM']:.2f} mm\n",
                )
            if "BARRAS_ACIMA_DESPERDICIO_RECOMENDADO" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Barras acima do recomendado: "
                    f"{int(row['BARRAS_ACIMA_DESPERDICIO_RECOMENDADO'])}\n",
                )
            if "MAIOR_DESPERDICIO_POR_BARRA_MM" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Maior desperdicio por barra: "
                    f"{row['MAIOR_DESPERDICIO_POR_BARRA_MM']:.2f} mm\n",
                )
            if "RETALHO_REAPROVEITAVEL_BARRAS" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Retalhos reaproveitaveis: {int(row['RETALHO_REAPROVEITAVEL_BARRAS'])} barra(s) | "
                    f"{row['RETALHO_REAPROVEITAVEL_MM']:.2f} mm\n",
                )
            else:
                texto.insert("end", f"  Retalho reaproveitavel: {row['RETALHO_REAPROVEITAVEL_MM']:.2f} mm\n")
            if "APROVEITAMENTO_PERCENTUAL" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Aproveitamento das barras de cobre: {row['APROVEITAMENTO_PERCENTUAL']:.2f}%\n",
                )
            texto.insert("end", f"  Status: {row['STATUS']}\n")
            texto.insert("end", "-" * 70 + "\n")

        if not faltas.empty:
            texto.insert(
                "end",
                "\nITENS NAO ATENDIDOS PELO ESTOQUE INFORMADO:\n"
                "(o Excel inclui o plano otimizado com barras padrao para completar estes itens)\n",
            )
            for _, row in faltas.iterrows():
                texto.insert(
                    "end",
                    f"  Ø{row['DIAMETRO']:g} | {row['COMPRIMENTO']:g} mm | "
                    f"faltam {int(row['QTD_FALTANTE'])} un\n",
                )

        texto.insert("end", f"\nExcel gerado em:\n{caminho_excel}\n")
        texto.config(state="disabled")

        botoes = ttk.Frame(janela)
        botoes.pack(pady=(0, 15))

        ttk.Button(
            botoes,
            text="Abrir Excel",
            command=lambda: self.abrir_arquivo(caminho_excel),
        ).pack(side="left", padx=5)

        ttk.Button(
            botoes,
            text="Abrir pasta",
            command=lambda: self.abrir_pasta(os.path.dirname(caminho_excel)),
        ).pack(side="left", padx=5)

        ttk.Button(
            botoes,
            text="Fechar",
            command=janela.destroy,
        ).pack(side="left", padx=5)

    @staticmethod
    def abrir_arquivo(caminho):
        try:
            os.startfile(caminho)
        except Exception:
            messagebox.showinfo("Arquivo", caminho)

    @staticmethod
    def abrir_pasta(caminho):
        try:
            os.startfile(caminho)
        except Exception:
            messagebox.showinfo("Pasta", caminho)



# =====================================================================
# PRINCIPIA MINIMA 3.0 INDUSTRIAL
# CAMADA DE MELHORIAS - CSPUL / PRINCIPIA LAB / HISTORICO / VISUAL
# =====================================================================
#
# Esta camada mantém os motores existentes e adiciona:
#
# 1) Leitura flexível de CSV/XLSX.
# 2) OFERTA e DATA preservadas para rastreabilidade.
# 3) Modelo V(r,phi) importado do Principia Lab.
# 4) Planejado lexicográfico:
#       Etapa 1: minimizar barras
#       Etapa 2: minimizar desperdício real
#       Etapa 3: minimizar fragmentação de retalhos
#       Etapa 4: maximizar valor futuro dos retalhos
# 5) Comparação do conjunto de retalhos "mínimo desperdício" x
#    "plano inteligente".
# 6) Banco histórico SQLite local (offline e sem servidor).
# 7) Estoque final simulado e envelhecimento/FIFO para auditoria.
# 8) Folha visual imprimível em HTML e animação do corte no Tkinter.
# 9) Logo MR opcional, selecionado pelo usuário.
#
# FUTURO:
# - Firestore/Firebase como camada central de sincronização.
# - Otimização multi-período completa.
# - Programação estocástica para demanda incerta.
# =====================================================================

VERSAO_INDUSTRIAL = "3.2 Factory Intelligence"
HORIZONTES_LAB = {
    "Média 15/30/60": "MEDIA",
    "15 dias": "15",
    "30 dias": "30",
    "60 dias": "60",
}
ESCALA_OBJETIVO = 1000


# =====================================================================
# PASTA DE DADOS / CONFIGURAÇÃO / BANCO LOCAL
# =====================================================================

def pasta_dados_principia():
    if os.name == "nt":
        base = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
        pasta = Path(base) / "PrincipiaMinima"
    else:
        pasta = Path.home() / ".principia_minima"

    pasta.mkdir(parents=True, exist_ok=True)
    return pasta


def caminho_banco_principia():
    return pasta_dados_principia() / "principia_minima_historico.db"


def caminho_config_principia():
    return pasta_dados_principia() / "config.json"


def carregar_config():
    p = caminho_config_principia()
    if not p.exists():
        return {}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {}


def salvar_config(config):
    caminho_config_principia().write_text(
        json.dumps(config, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def inicializar_banco():
    caminho = caminho_banco_principia()

    with sqlite3.connect(caminho) as con:
        con.execute(
            """
            CREATE TABLE IF NOT EXISTS execucoes (
                id_execucao TEXT PRIMARY KEY,
                data_hora TEXT NOT NULL,
                versao TEXT NOT NULL,
                modo TEXT NOT NULL,
                arquivo_demanda TEXT,
                arquivo_estoque TEXT,
                arquivo_lab TEXT,
                horizonte_lab TEXT,
                parametros_json TEXT,
                resumo_json TEXT,
                excel_saida TEXT,
                folha_visual TEXT
            )
            """
        )

        con.execute(
            """
            CREATE TABLE IF NOT EXISTS retalhos (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                id_execucao TEXT NOT NULL,
                diametro REAL NOT NULL,
                comprimento_mm REAL NOT NULL,
                classificacao TEXT NOT NULL,
                valor_v15 REAL,
                valor_v30 REAL,
                valor_v60 REAL,
                valor_criterio REAL,
                FOREIGN KEY(id_execucao) REFERENCES execucoes(id_execucao)
            )
            """
        )

        con.execute(
            """
            CREATE TABLE IF NOT EXISTS estoque_snapshot (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                id_execucao TEXT NOT NULL,
                tipo_snapshot TEXT NOT NULL,
                diametro REAL,
                comprimento_mm REAL,
                quantidade INTEGER,
                data_entrada TEXT,
                idade_dias INTEGER,
                FOREIGN KEY(id_execucao) REFERENCES execucoes(id_execucao)
            )
            """
        )

        con.commit()

    return caminho


def _json_default(obj):
    if isinstance(obj, (datetime, pd.Timestamp)):
        return obj.isoformat()
    if isinstance(obj, np.generic):
        return obj.item()
    return str(obj)


def registrar_execucao_historico(
    modo,
    arquivo_demanda,
    resumo,
    plano,
    excel_saida,
    folha_visual=None,
    arquivo_estoque=None,
    arquivo_lab=None,
    horizonte_lab=None,
    parametros=None,
    estoque_inicial=None,
    estoque_final=None,
):
    inicializar_banco()
    id_execucao = f"PM-{datetime.now():%Y%m%d-%H%M%S}-{uuid.uuid4().hex[:6].upper()}"

    resumo_json = (
        resumo.to_dict(orient="records")
        if isinstance(resumo, pd.DataFrame)
        else resumo
    )

    with sqlite3.connect(caminho_banco_principia()) as con:
        con.execute(
            """
            INSERT INTO execucoes (
                id_execucao, data_hora, versao, modo,
                arquivo_demanda, arquivo_estoque, arquivo_lab,
                horizonte_lab, parametros_json, resumo_json,
                excel_saida, folha_visual
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                id_execucao,
                datetime.now().isoformat(timespec="seconds"),
                VERSAO_INDUSTRIAL,
                modo,
                arquivo_demanda or "",
                arquivo_estoque or "",
                arquivo_lab or "",
                horizonte_lab or "",
                json.dumps(parametros or {}, ensure_ascii=False, default=_json_default),
                json.dumps(resumo_json or [], ensure_ascii=False, default=_json_default),
                excel_saida or "",
                folha_visual or "",
            ),
        )

        if isinstance(plano, pd.DataFrame) and not plano.empty:
            for _, row in plano.iterrows():
                sobra = float(row.get("SOBRA_POR_BARRA_MM", 0) or 0)
                classificacao = str(row.get("CLASSIFICACAO_SOBRA", ""))
                if sobra <= 0:
                    continue

                con.execute(
                    """
                    INSERT INTO retalhos (
                        id_execucao, diametro, comprimento_mm,
                        classificacao, valor_v15, valor_v30,
                        valor_v60, valor_criterio
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        id_execucao,
                        float(row.get("DIAMETRO", 0) or 0),
                        sobra,
                        classificacao,
                        _float_or_none(row.get("VALOR_V15_MM")),
                        _float_or_none(row.get("VALOR_V30_MM")),
                        _float_or_none(row.get("VALOR_V60_MM")),
                        _float_or_none(row.get("VALOR_FUTURO_CRITERIO_MM")),
                    ),
                )

        for tipo_snapshot, estoque in (
            ("INICIAL", estoque_inicial),
            ("FINAL", estoque_final),
        ):
            if isinstance(estoque, pd.DataFrame) and not estoque.empty:
                for _, row in estoque.iterrows():
                    con.execute(
                        """
                        INSERT INTO estoque_snapshot (
                            id_execucao, tipo_snapshot, diametro,
                            comprimento_mm, quantidade, data_entrada, idade_dias
                        ) VALUES (?, ?, ?, ?, ?, ?, ?)
                        """,
                        (
                            id_execucao,
                            tipo_snapshot,
                            _float_or_none(row.get("DIAMETRO")),
                            _float_or_none(row.get("COMPRIMENTO")),
                            int(row.get("QUANTIDADE", 0) or 0),
                            str(row.get("DATA_ENTRADA", "") or ""),
                            int(row.get("IDADE_DIAS", 0) or 0),
                        ),
                    )

        con.commit()

    return id_execucao


def _float_or_none(valor):
    try:
        if valor is None or pd.isna(valor):
            return None
        return float(valor)
    except Exception:
        return None


def ler_historico_execucoes(limite=200):
    inicializar_banco()

    with sqlite3.connect(caminho_banco_principia()) as con:
        return pd.read_sql_query(
            """
            SELECT id_execucao, data_hora, versao, modo,
                   arquivo_demanda, horizonte_lab,
                   excel_saida, folha_visual
            FROM execucoes
            ORDER BY data_hora DESC
            LIMIT ?
            """,
            con,
            params=(int(limite),),
        )


# =====================================================================
# LEITURA FLEXÍVEL CSV / EXCEL
# =====================================================================

def _normalizar_nome_coluna_v3(nome):
    import unicodedata

    texto = unicodedata.normalize("NFKD", str(nome))
    texto = "".join(
        c for c in texto
        if not unicodedata.combining(c)
    )
    texto = texto.strip().upper()
    texto = re.sub(r"\s+", "_", texto)
    return texto


def _ler_tabela_flexivel(caminho):
    extensao = Path(caminho).suffix.lower()

    if extensao in (".xlsx", ".xlsm", ".xls"):
        df = pd.read_excel(caminho, dtype=str)
    elif extensao == ".csv":
        try:
            df = pd.read_csv(caminho, sep=None, engine="python", dtype=str)
        except Exception:
            df = pd.read_csv(caminho, sep=";", dtype=str)
    else:
        raise ValueError("Use arquivo .csv, .xlsx, .xlsm ou .xls.")

    df.columns = [
        _normalizar_nome_coluna_v3(c)
        for c in df.columns
    ]
    return df


def ler_demanda_csv(caminho):
    """
    V3: mantém o nome da função por compatibilidade, mas aceita CSV ou Excel.

    Formato mínimo:
        DIAMETRO | COMPRIMENTO | DEMANDA

    Formato recomendado:
        DATA | PIV | OFERTA | LINHA | DIAMETRO | COMPRIMENTO | DEMANDA
    """
    df = _ler_tabela_flexivel(caminho)

    necessarias = {"DIAMETRO", "COMPRIMENTO", "DEMANDA"}
    faltantes = necessarias - set(df.columns)
    if faltantes:
        raise ValueError(
            "A demanda precisa conter DIAMETRO, COMPRIMENTO e DEMANDA.\n"
            f"Colunas ausentes: {sorted(faltantes)}"
        )

    for opcional, padrao in (
        ("PIV", "SEM_PIV"),
        ("OFERTA", "SEM_OFERTA"),
        ("LINHA", "SEM_LINHA"),
        ("DATA", ""),
    ):
        if opcional not in df.columns:
            df[opcional] = padrao

    df = df[
        [
            "DATA",
            "PIV",
            "OFERTA",
            "LINHA",
            "DIAMETRO",
            "COMPRIMENTO",
            "DEMANDA",
        ]
    ].copy()

    df["_ORDEM"] = range(len(df))
    df = df.dropna(
        subset=["DIAMETRO", "COMPRIMENTO", "DEMANDA"]
    )

    if df.empty:
        raise ValueError("A planilha de demanda está vazia.")

    for col, padrao in (
        ("PIV", "SEM_PIV"),
        ("OFERTA", "SEM_OFERTA"),
        ("LINHA", "SEM_LINHA"),
    ):
        df[col] = df[col].fillna(padrao).astype(str).str.strip()
        df.loc[df[col] == "", col] = padrao

    df["DIAMETRO"] = _normalizar_numero(df["DIAMETRO"])
    df["COMPRIMENTO"] = _normalizar_numero(df["COMPRIMENTO"])
    df["DEMANDA"] = _normalizar_numero(df["DEMANDA"])

    if df[["DIAMETRO", "COMPRIMENTO", "DEMANDA"]].isna().any().any():
        raise ValueError(
            "Existem valores inválidos em DIAMETRO, COMPRIMENTO ou DEMANDA."
        )

    if (
        (df["DIAMETRO"] <= 0).any()
        or (df["COMPRIMENTO"] <= 0).any()
        or (df["DEMANDA"] <= 0).any()
    ):
        raise ValueError("Diâmetro, comprimento e demanda devem ser positivos.")

    if ((df["DEMANDA"] % 1) != 0).any():
        raise ValueError("DEMANDA deve conter apenas números inteiros.")

    df["DEMANDA"] = df["DEMANDA"].astype(int)
    df["DIAMETRO"] = df["DIAMETRO"].round(4)
    df["COMPRIMENTO"] = df["COMPRIMENTO"].round(4)

    # DATA é informativa no motor atual e será base para o multi-período futuro.
    if "DATA" in df.columns:
        df["DATA"] = pd.to_datetime(
            df["DATA"],
            errors="coerce",
            dayfirst=True,
        )

    return df.sort_values("_ORDEM").reset_index(drop=True)


def ler_estoque_csv(caminho, barra_padrao):
    """
    V3: CSV ou Excel.

    Colunas mínimas:
        DIAMETRO | COMPRIMENTO | QUANTIDADE

    Recomendadas:
        ID_RETALHO | DATA_ENTRADA | DIAMETRO | COMPRIMENTO | QUANTIDADE

    DATA_ENTRADA permite acompanhar o envelhecimento do estoque.
    """
    df = _ler_tabela_flexivel(caminho)

    necessarias = {"DIAMETRO", "COMPRIMENTO", "QUANTIDADE"}
    faltantes = necessarias - set(df.columns)
    if faltantes:
        raise ValueError(
            "O estoque precisa conter DIAMETRO, COMPRIMENTO e QUANTIDADE.\n"
            f"Colunas ausentes: {sorted(faltantes)}"
        )

    if "DATA_ENTRADA" not in df.columns:
        df["DATA_ENTRADA"] = datetime.now().date().isoformat()

    if "ID_RETALHO" not in df.columns:
        df["ID_RETALHO"] = [
            f"EST-{i+1:05d}"
            for i in range(len(df))
        ]

    df = df[
        [
            "ID_RETALHO",
            "DATA_ENTRADA",
            "DIAMETRO",
            "COMPRIMENTO",
            "QUANTIDADE",
        ]
    ].copy()

    df["DIAMETRO"] = _normalizar_numero(df["DIAMETRO"])
    df["COMPRIMENTO"] = _normalizar_numero(df["COMPRIMENTO"])
    df["QUANTIDADE"] = _normalizar_numero(df["QUANTIDADE"])

    if df[["DIAMETRO", "COMPRIMENTO", "QUANTIDADE"]].isna().any().any():
        raise ValueError("Existem valores numéricos inválidos no estoque.")

    if (
        (df["DIAMETRO"] <= 0).any()
        or (df["COMPRIMENTO"] <= 0).any()
        or (df["QUANTIDADE"] <= 0).any()
    ):
        raise ValueError("Os valores do estoque devem ser positivos.")

    if ((df["QUANTIDADE"] % 1) != 0).any():
        raise ValueError("QUANTIDADE deve conter números inteiros.")

    df["QUANTIDADE"] = df["QUANTIDADE"].astype(int)
    df["DIAMETRO"] = df["DIAMETRO"].round(4)
    df["COMPRIMENTO"] = df["COMPRIMENTO"].round(4)

    df["DATA_ENTRADA"] = pd.to_datetime(
        df["DATA_ENTRADA"],
        errors="coerce",
        dayfirst=True,
    )
    df["DATA_ENTRADA"] = df["DATA_ENTRADA"].fillna(
        pd.Timestamp(datetime.now().date())
    )

    hoje = pd.Timestamp(datetime.now().date())
    df["IDADE_DIAS"] = (
        hoje - df["DATA_ENTRADA"].dt.normalize()
    ).dt.days.clip(lower=0)

    df["TIPO"] = df["COMPRIMENTO"].apply(
        lambda c: (
            "NOVA"
            if abs(float(c) - float(barra_padrao)) <= 1e-6
            else "RETALHO"
        )
    )

    return (
        df.groupby(
            [
                "TIPO",
                "DATA_ENTRADA",
                "IDADE_DIAS",
                "DIAMETRO",
                "COMPRIMENTO",
            ],
            as_index=False,
        )["QUANTIDADE"]
        .sum()
        .sort_values(
            ["DIAMETRO", "TIPO", "IDADE_DIAS", "COMPRIMENTO"],
            ascending=[True, True, False, False],
        )
        .reset_index(drop=True)
    )


# =====================================================================
# RASTREABILIDADE V3 - OFERTA
# =====================================================================

def adicionar_rastreabilidade_ao_plano(plano, demanda_detalhada):
    if plano.empty:
        return plano.copy()

    filas = {}
    demanda_ord = demanda_detalhada.sort_values("_ORDEM").copy()

    for _, row in demanda_ord.iterrows():
        chave = (
            round(float(row["DIAMETRO"]), 4),
            round(float(row["COMPRIMENTO"]), 4),
        )
        filas.setdefault(chave, []).append(
            {
                "PIV": str(row.get("PIV", "SEM_PIV")),
                "OFERTA": str(row.get("OFERTA", "SEM_OFERTA")),
                "LINHA": str(row.get("LINHA", "SEM_LINHA")),
                "restante": int(row["DEMANDA"]),
            }
        )

    linhas_expandidas = []
    contador_barra = 1

    for _, row in plano.iterrows():
        qtd_barras = int(row.get("QTD_BARRAS", 1))
        cortes = _extrair_cortes_do_esquema(
            row.get("ESQUEMA_DE_CORTE", "")
        )

        for _ in range(qtd_barras):
            nova = row.to_dict()
            nova["QTD_BARRAS"] = 1
            nova["ID_PADRAO_ORIGINAL"] = nova.get("ID_PADRAO", "")
            nova["ID_BARRA"] = f"B{contador_barra:04d}"

            referencias = []

            for comp, qtd in cortes:
                chave = (
                    round(float(row["DIAMETRO"]), 4),
                    round(float(comp), 4),
                )
                fila = filas.get(chave, [])
                faltam = int(qtd)

                while faltam > 0 and fila:
                    pedido = fila[0]
                    usar = min(faltam, pedido["restante"])

                    referencias.append(
                        {
                            "PIV": pedido["PIV"],
                            "OFERTA": pedido["OFERTA"],
                            "LINHA": pedido["LINHA"],
                            "COMPRIMENTO": comp,
                            "QTD": usar,
                        }
                    )

                    pedido["restante"] -= usar
                    faltam -= usar

                    if pedido["restante"] <= 0:
                        fila.pop(0)

                if faltam > 0:
                    referencias.append(
                        {
                            "PIV": "SEM_REFERENCIA",
                            "OFERTA": "SEM_REFERENCIA",
                            "LINHA": "SEM_REFERENCIA",
                            "COMPRIMENTO": comp,
                            "QTD": faltam,
                        }
                    )

            consolidadas = []
            mapa = {}

            for ref in referencias:
                chave_ref = (
                    ref["PIV"],
                    ref["OFERTA"],
                    ref["LINHA"],
                    round(ref["COMPRIMENTO"], 4),
                )

                if chave_ref not in mapa:
                    mapa[chave_ref] = len(consolidadas)
                    consolidadas.append(ref.copy())
                else:
                    consolidadas[mapa[chave_ref]]["QTD"] += ref["QTD"]

            nova["PIV_OFERTA_LINHAS_ATENDIDAS"] = "; ".join(
                (
                    f"PIV {ref['PIV']} / Oferta {ref['OFERTA']} / "
                    f"Linha {ref['LINHA']} -> "
                    f"{ref['QTD']}x({ref['COMPRIMENTO']:g}mm)"
                )
                for ref in consolidadas
            )

            nova["PIV_LINHAS_ATENDIDAS"] = "; ".join(
                (
                    f"PIV {ref['PIV']} / Linha {ref['LINHA']} -> "
                    f"{ref['QTD']}x({ref['COMPRIMENTO']:g}mm)"
                )
                for ref in consolidadas
            )

            linhas_expandidas.append(nova)
            contador_barra += 1

    return pd.DataFrame(linhas_expandidas)


# =====================================================================
# MODELO DE VALOR DO PRINCIPIA LAB
# =====================================================================

class ModeloValorRetalho:
    """
    Carrega a aba VALOR_RETALHOS do Principia Lab.

    Para sobras entre dois pontos testados pelo Lab, usa interpolação
    linear. Abaixo do primeiro ponto com valor conhecido, retorna zero.
    Acima do maior ponto, mantém o último valor conhecido (conservador).
    """

    def __init__(self, caminho_excel=None, horizonte="MEDIA"):
        self.caminho_excel = caminho_excel
        self.horizonte = str(horizonte or "MEDIA").upper()
        self.df = pd.DataFrame()

        if caminho_excel:
            self.df = pd.read_excel(
                caminho_excel,
                sheet_name="VALOR_RETALHOS",
            )
            self.df.columns = [
                _normalizar_nome_coluna_v3(c)
                for c in self.df.columns
            ]

            obrigatorias = {"DIAMETRO", "RETALHO_MM"}
            if not obrigatorias.issubset(self.df.columns):
                raise ValueError(
                    "Arquivo do Principia Lab inválido: "
                    "a aba VALOR_RETALHOS não possui DIAMETRO e RETALHO_MM."
                )

            self.df["DIAMETRO"] = pd.to_numeric(
                self.df["DIAMETRO"],
                errors="coerce",
            )
            self.df["RETALHO_MM"] = pd.to_numeric(
                self.df["RETALHO_MM"],
                errors="coerce",
            )
            self.df = self.df.dropna(
                subset=["DIAMETRO", "RETALHO_MM"]
            )

    @property
    def disponivel(self):
        return not self.df.empty

    def _coluna(self, horizonte=None):
        h = str(horizonte or self.horizonte).upper()

        if h == "15":
            return "V15_MM"
        if h == "30":
            return "V30_MM"
        if h == "60":
            return "V60_MM"
        return "VALOR_MEDIO_HORIZONTES_MM"

    def valor(self, diametro, retalho_mm, horizonte=None):
        if not self.disponivel or retalho_mm <= 0:
            return 0.0

        grupo = self.df[
            np.isclose(
                pd.to_numeric(
                    self.df["DIAMETRO"],
                    errors="coerce",
                ).astype(float),
                float(diametro),
                atol=1e-6,
            )
        ].copy()

        if grupo.empty:
            return 0.0

        coluna = self._coluna(horizonte)

        if coluna not in grupo.columns:
            return 0.0

        grupo[coluna] = pd.to_numeric(
            grupo[coluna],
            errors="coerce",
        )
        grupo = (
            grupo.dropna(subset=[coluna])
            .sort_values("RETALHO_MM")
            .drop_duplicates("RETALHO_MM", keep="last")
        )

        if grupo.empty:
            return 0.0

        xs = grupo["RETALHO_MM"].astype(float).to_numpy()
        ys = grupo[coluna].astype(float).to_numpy()
        r = float(retalho_mm)

        if r < xs.min():
            return 0.0

        if r >= xs.max():
            return float(ys[-1])

        return float(np.interp(r, xs, ys))

    def valores_horizontes(self, diametro, retalho_mm):
        return {
            "V15_MM": self.valor(diametro, retalho_mm, "15"),
            "V30_MM": self.valor(diametro, retalho_mm, "30"),
            "V60_MM": self.valor(diametro, retalho_mm, "60"),
            "VALOR_FUTURO_CRITERIO_MM": self.valor(
                diametro,
                retalho_mm,
                self.horizonte,
            ),
        }


def score_fallback_quadratico(sobra_mm, tamanho_fonte):
    """
    Fallback inspirado na concentração de sobras:
    soma dos quadrados favorece poucos retalhos maiores.

    Divide por tamanho_fonte apenas para manter a escala próxima de mm.
    """
    if sobra_mm <= 0 or tamanho_fonte <= 0:
        return 0.0
    return (float(sobra_mm) ** 2) / float(tamanho_fonte)


def valor_futuro_padrao(
    diametro,
    sobra,
    limite_retalho,
    tamanho_fonte,
    modelo_valor=None,
):
    if sobra < limite_retalho:
        return 0.0

    if modelo_valor is not None and modelo_valor.disponivel:
        # Se o Lab disser que o valor histórico é zero, zero é informação.
        # Não substituímos esse resultado por um fallback artificial.
        return modelo_valor.valor(
            diametro,
            sobra,
        )

    return score_fallback_quadratico(
        sobra,
        tamanho_fonte,
    )


def anotar_valor_retalhos(
    plano,
    modelo_valor,
    limite_retalho,
    horizonte="MEDIA",
):
    if plano.empty:
        return plano.copy()

    df = plano.copy()

    v15 = []
    v30 = []
    v60 = []
    criterio = []

    for _, row in df.iterrows():
        sobra = float(row.get("SOBRA_POR_BARRA_MM", 0) or 0)
        diam = float(row.get("DIAMETRO", 0) or 0)
        fonte = float(row.get("COMPRIMENTO_FONTE_MM", 1) or 1)

        if sobra < limite_retalho:
            valores = {
                "V15_MM": 0.0,
                "V30_MM": 0.0,
                "V60_MM": 0.0,
                "VALOR_FUTURO_CRITERIO_MM": 0.0,
            }
        elif modelo_valor is not None and modelo_valor.disponivel:
            valores = modelo_valor.valores_horizontes(
                diam,
                sobra,
            )
            valores["VALOR_FUTURO_CRITERIO_MM"] = modelo_valor.valor(
                diam,
                sobra,
                horizonte,
            )
        else:
            fallback = score_fallback_quadratico(
                sobra,
                fonte,
            )
            valores = {
                "V15_MM": np.nan,
                "V30_MM": np.nan,
                "V60_MM": np.nan,
                "VALOR_FUTURO_CRITERIO_MM": fallback,
            }

        v15.append(valores["V15_MM"])
        v30.append(valores["V30_MM"])
        v60.append(valores["V60_MM"])
        criterio.append(valores["VALOR_FUTURO_CRITERIO_MM"])

    df["VALOR_V15_MM"] = v15
    df["VALOR_V30_MM"] = v30
    df["VALOR_V60_MM"] = v60
    df["VALOR_FUTURO_CRITERIO_MM"] = criterio
    df["HORIZONTE_VALOR"] = str(horizonte)

    return df


# =====================================================================
# PLANEJADO V3 - OBJETIVO LEXICOGRÁFICO CSPUL
# =====================================================================

def _resolver_etapa(
    solver,
    inicio_otimizacao,
    limite_etapa_ms=None,
):
    restante = tempo_restante_otimizacao_ms(
        inicio_otimizacao
    )

    if restante <= 0:
        return None

    if limite_etapa_ms is not None:
        restante = min(
            restante,
            int(limite_etapa_ms),
        )

    solver.SetTimeLimit(
        max(1, int(restante))
    )
    return solver.Solve()


def _metricas_conjunto_retalhos(
    valores,
    sobras,
    desperdicios,
    futuros,
    limite_retalho,
):
    total_desperdicio = 0.0
    total_retalho = 0.0
    qtd_retalhos = 0
    valor_futuro = 0.0
    quadrados = 0.0
    maior = 0.0

    for j, vezes in enumerate(valores):
        vezes = int(vezes)
        if vezes <= 0:
            continue

        total_desperdicio += desperdicios[j] * vezes

        if sobras[j] >= limite_retalho:
            qtd_retalhos += vezes
            total_retalho += sobras[j] * vezes
            valor_futuro += futuros[j] * vezes
            quadrados += (sobras[j] ** 2) * vezes
            maior = max(maior, sobras[j])

    medio = (
        total_retalho / qtd_retalhos
        if qtd_retalhos
        else 0.0
    )

    concentracao = (
        quadrados / (total_retalho ** 2)
        if total_retalho > 0
        else 0.0
    )

    return {
        "DESPERDICIO_REAL_MM": round(total_desperdicio, 3),
        "QTD_RETALHOS_REAPROVEITAVEIS": int(qtd_retalhos),
        "RETALHO_REAPROVEITAVEL_TOTAL_MM": round(total_retalho, 3),
        "RETALHO_MEDIO_MM": round(medio, 3),
        "MAIOR_RETALHO_MM": round(maior, 3),
        "VALOR_FUTURO_TOTAL": round(valor_futuro, 3),
        "INDICE_CONCENTRACAO": round(concentracao, 6),
    }


def otimizar_planejado_por_diametro(
    diametro,
    df_demanda_diametro,
    tamanho_barra,
    kerf,
    limite_retalho,
    desperdicio_max_recomendado,
    modelo_valor=None,
):
    comprimentos = sorted(
        df_demanda_diametro["COMPRIMENTO"].astype(float).tolist(),
        reverse=True,
    )

    demanda_map = dict(
        zip(
            df_demanda_diametro["COMPRIMENTO"].astype(float),
            df_demanda_diametro["DEMANDA"].astype(int),
        )
    )
    demandas = [
        demanda_map[c]
        for c in comprimentos
    ]

    invalidas = [
        c for c in comprimentos
        if c + kerf > tamanho_barra
    ]

    if invalidas:
        raise ValueError(
            f"Diâmetro {diametro}: peças maiores que "
            f"a barra padrão de {tamanho_barra} mm: {invalidas}"
        )

    padroes = gerar_padroes_completos(
        comprimentos,
        demandas,
        tamanho_barra,
        kerf,
    )

    if not padroes:
        raise RuntimeError(
            f"Diâmetro {diametro}: nenhum padrão viável foi gerado."
        )

    sobras = [
        calcular_sobra(
            p,
            comprimentos,
            tamanho_barra,
            kerf,
        )
        for p in padroes
    ]

    desperdicios = [
        s if s < limite_retalho else 0.0
        for s in sobras
    ]

    retalho_bin = [
        1 if s >= limite_retalho else 0
        for s in sobras
    ]

    valores_futuros = [
        valor_futuro_padrao(
            diametro,
            s,
            limite_retalho,
            tamanho_barra,
            modelo_valor,
        )
        for s in sobras
    ]

    desperdicios_int = [
        int(round(d * ESCALA_OBJETIVO))
        for d in desperdicios
    ]

    futuros_int = [
        int(round(v * ESCALA_OBJETIVO))
        for v in valores_futuros
    ]

    inicio = time.monotonic()

    # ---------------------------------------------------------
    # ETAPA 1 - MENOR NÚMERO DE BARRAS
    # ---------------------------------------------------------
    solver1 = criar_solver()
    x1 = [
        solver1.IntVar(
            0,
            solver1.infinity(),
            f"x1_{j}",
        )
        for j in range(len(padroes))
    ]

    for i, demanda in enumerate(demandas):
        solver1.Add(
            solver1.Sum(
                padroes[j][i] * x1[j]
                for j in range(len(padroes))
            )
            == demanda
        )

    solver1.Minimize(
        solver1.Sum(x1)
    )

    status1 = _resolver_etapa(
        solver1,
        inicio,
        30000,
    )

    if status1 not in (
        pywraplp.Solver.OPTIMAL,
        pywraplp.Solver.FEASIBLE,
    ):
        raise RuntimeError(
            f"Diâmetro {diametro}: não foi encontrada solução viável."
        )

    valores1 = [
        int(round(v.solution_value()))
        for v in x1
    ]
    minimo_barras = int(
        round(sum(valores1))
    )

    valores_finais = valores1
    baseline_valores = valores1
    status_texto = (
        "Melhor solução viável em número de barras; ótimo não comprovado"
    )

    if status1 == pywraplp.Solver.OPTIMAL:
        status_texto = "Etapa 1 ótima: mínimo de barras comprovado"

        # -----------------------------------------------------
        # ETAPA 2 - MENOR DESPERDÍCIO REAL
        # -----------------------------------------------------
        solver2 = criar_solver()
        x2 = [
            solver2.IntVar(
                0,
                solver2.infinity(),
                f"x2_{j}",
            )
            for j in range(len(padroes))
        ]

        for i, demanda in enumerate(demandas):
            solver2.Add(
                solver2.Sum(
                    padroes[j][i] * x2[j]
                    for j in range(len(padroes))
                )
                == demanda
            )

        solver2.Add(
            solver2.Sum(x2) == minimo_barras
        )

        desperdicio_expr2 = solver2.Sum(
            desperdicios_int[j] * x2[j]
            for j in range(len(padroes))
        )

        solver2.Minimize(
            desperdicio_expr2
        )

        try:
            solver2.SetHint(
                x2,
                [
                    x1[j].solution_value()
                    for j in range(len(x1))
                ],
            )
        except Exception:
            pass

        status2 = _resolver_etapa(
            solver2,
            inicio,
            12000,
        )

        if status2 in (
            pywraplp.Solver.OPTIMAL,
            pywraplp.Solver.FEASIBLE,
        ):
            valores2 = [
                int(round(v.solution_value()))
                for v in x2
            ]
            valores_finais = valores2
            baseline_valores = valores2

            melhor_desperdicio_int = sum(
                desperdicios_int[j] * valores2[j]
                for j in range(len(padroes))
            )

            status_texto = (
                "Etapa 2 ótima: mínimo de barras e desperdício comprovados"
                if status2 == pywraplp.Solver.OPTIMAL
                else "Etapa 2 viável: mínimo de barras comprovado; "
                     "menor desperdício não comprovado"
            )

            # Etapas 3 e 4 só avançam se o mínimo de desperdício
            # foi comprovado. Assim o objetivo lexicográfico é respeitado.
            if (
                status2 == pywraplp.Solver.OPTIMAL
                and tempo_restante_otimizacao_ms(inicio) > 0
            ):
                # ---------------------------------------------
                # ETAPA 3 - MENOR FRAGMENTAÇÃO
                # ---------------------------------------------
                solver3 = criar_solver()
                x3 = [
                    solver3.IntVar(
                        0,
                        solver3.infinity(),
                        f"x3_{j}",
                    )
                    for j in range(len(padroes))
                ]

                for i, demanda in enumerate(demandas):
                    solver3.Add(
                        solver3.Sum(
                            padroes[j][i] * x3[j]
                            for j in range(len(padroes))
                        )
                        == demanda
                    )

                solver3.Add(
                    solver3.Sum(x3) == minimo_barras
                )
                solver3.Add(
                    solver3.Sum(
                        desperdicios_int[j] * x3[j]
                        for j in range(len(padroes))
                    )
                    == melhor_desperdicio_int
                )

                qtd_retalhos_expr3 = solver3.Sum(
                    retalho_bin[j] * x3[j]
                    for j in range(len(padroes))
                )

                solver3.Minimize(
                    qtd_retalhos_expr3
                )

                try:
                    solver3.SetHint(
                        x3,
                        [
                            x2[j].solution_value()
                            for j in range(len(x2))
                        ],
                    )
                except Exception:
                    pass

                status3 = _resolver_etapa(
                    solver3,
                    inicio,
                    8000,
                )

                if status3 in (
                    pywraplp.Solver.OPTIMAL,
                    pywraplp.Solver.FEASIBLE,
                ):
                    valores3 = [
                        int(round(v.solution_value()))
                        for v in x3
                    ]
                    valores_finais = valores3

                    minimo_retalhos = sum(
                        retalho_bin[j] * valores3[j]
                        for j in range(len(padroes))
                    )

                    status_texto = (
                        "Etapa 3 ótima: barras, desperdício e fragmentação "
                        "minimizados"
                        if status3 == pywraplp.Solver.OPTIMAL
                        else "Etapa 3 viável: fragmentação melhorada, "
                             "ótimo não comprovado"
                    )

                    # -----------------------------------------
                    # ETAPA 4 - MAIOR VALOR FUTURO
                    # -----------------------------------------
                    if (
                        status3 == pywraplp.Solver.OPTIMAL
                        and tempo_restante_otimizacao_ms(inicio) > 0
                    ):
                        solver4 = criar_solver()
                        x4 = [
                            solver4.IntVar(
                                0,
                                solver4.infinity(),
                                f"x4_{j}",
                            )
                            for j in range(len(padroes))
                        ]

                        for i, demanda in enumerate(demandas):
                            solver4.Add(
                                solver4.Sum(
                                    padroes[j][i] * x4[j]
                                    for j in range(len(padroes))
                                )
                                == demanda
                            )

                        solver4.Add(
                            solver4.Sum(x4) == minimo_barras
                        )

                        solver4.Add(
                            solver4.Sum(
                                desperdicios_int[j] * x4[j]
                                for j in range(len(padroes))
                            )
                            == melhor_desperdicio_int
                        )

                        solver4.Add(
                            solver4.Sum(
                                retalho_bin[j] * x4[j]
                                for j in range(len(padroes))
                            )
                            == minimo_retalhos
                        )

                        solver4.Maximize(
                            solver4.Sum(
                                futuros_int[j] * x4[j]
                                for j in range(len(padroes))
                            )
                        )

                        try:
                            solver4.SetHint(
                                x4,
                                [
                                    x3[j].solution_value()
                                    for j in range(len(x3))
                                ],
                            )
                        except Exception:
                            pass

                        status4 = _resolver_etapa(
                            solver4,
                            inicio,
                            None,
                        )

                        if status4 in (
                            pywraplp.Solver.OPTIMAL,
                            pywraplp.Solver.FEASIBLE,
                        ):
                            valores4 = [
                                int(round(v.solution_value()))
                                for v in x4
                            ]
                            valores_finais = valores4

                            fonte_valor = (
                                "Principia Lab"
                                if (
                                    modelo_valor is not None
                                    and modelo_valor.disponivel
                                )
                                else "soma dos quadrados / fallback"
                            )

                            status_texto = (
                                "Otimização lexicográfica completa: "
                                "barras → desperdício → fragmentação → "
                                f"valor futuro ({fonte_valor})"
                                if status4 == pywraplp.Solver.OPTIMAL
                                else "Melhor solução viável na Etapa 4; "
                                     f"valor futuro calculado por {fonte_valor}"
                            )

    metricas_baseline = _metricas_conjunto_retalhos(
        baseline_valores,
        sobras,
        desperdicios,
        valores_futuros,
        limite_retalho,
    )

    metricas_final = _metricas_conjunto_retalhos(
        valores_finais,
        sobras,
        desperdicios,
        valores_futuros,
        limite_retalho,
    )

    comparacao = []

    for nome, met in (
        ("BASE_MIN_DESPERDICIO", metricas_baseline),
        ("PLANO_INTELIGENTE", metricas_final),
    ):
        linha = {
            "DIAMETRO": diametro,
            "CENARIO": nome,
            "BARRAS": minimo_barras,
        }
        linha.update(met)
        comparacao.append(linha)

    linhas_plano = []
    total_desperdicio = 0.0
    total_retalho = 0.0
    total_sobra = 0.0
    id_padrao = 1

    for j, vezes in enumerate(valores_finais):
        if vezes <= 0:
            continue

        padrao = padroes[j]
        sobra = sobras[j]

        total_sobra += sobra * vezes

        if sobra >= limite_retalho:
            total_retalho += sobra * vezes
            classificacao = "RETALHO REAPROVEITAVEL"
        else:
            total_desperdicio += sobra * vezes
            classificacao = "DESPERDICIO"

        partes = []

        for qtd, comp in zip(
            padrao,
            comprimentos,
        ):
            if qtd > 0:
                partes.append(
                    f"{qtd}x({comp:g}mm)"
                )

        dados_valor = {
            "VALOR_V15_MM": np.nan,
            "VALOR_V30_MM": np.nan,
            "VALOR_V60_MM": np.nan,
            "VALOR_FUTURO_CRITERIO_MM": valores_futuros[j],
        }

        if (
            sobra >= limite_retalho
            and modelo_valor is not None
            and modelo_valor.disponivel
        ):
            dados_valor = modelo_valor.valores_horizontes(
                diametro,
                sobra,
            )

        linhas_plano.append(
            {
                "MODO": "PLANEJADO",
                "DIAMETRO": diametro,
                "ID_PADRAO": f"P{diametro:g}-{id_padrao}",
                "TIPO_FONTE": "NOVA",
                "COMPRIMENTO_FONTE_MM": tamanho_barra,
                "QTD_BARRAS": vezes,
                "ESQUEMA_DE_CORTE": " + ".join(partes),
                "SOBRA_POR_BARRA_MM": sobra,
                "CLASSIFICACAO_SOBRA": classificacao,
                **dados_valor,
            }
        )
        id_padrao += 1

    demanda_total_mm = sum(
        c * d
        for c, d in zip(
            comprimentos,
            demandas,
        )
    )

    material_total_mm = minimo_barras * tamanho_barra
    aproveitamento_percentual = (
        100.0 * demanda_total_mm / material_total_mm
        if material_total_mm > 0
        else 0.0
    )

    retalhos_gerados_barras = metricas_final[
        "QTD_RETALHOS_REAPROVEITAVEIS"
    ]

    barras_acima_desperdicio_recomendado = sum(
        int(vezes)
        for j, vezes in enumerate(valores_finais)
        if (
            vezes > 0
            and desperdicios[j] > desperdicio_max_recomendado
        )
    )

    maior_desperdicio_por_barra = max(
        (
            desperdicios[j]
            for j, vezes in enumerate(valores_finais)
            if vezes > 0
        ),
        default=0.0,
    )

    resumo = {
        "DIAMETRO": diametro,
        "DEMANDA_TOTAL_PECAS": int(sum(demandas)),
        "DEMANDA_TOTAL_MM": round(demanda_total_mm, 2),
        "PECAS_ATENDIDAS": int(sum(demandas)),
        "PECAS_FALTANTES": 0,
        "BARRAS_NOVAS_USADAS": minimo_barras,
        "RETALHOS_USADOS": 0,
        "TOTAL_FONTES_USADAS": minimo_barras,
        "SOBRA_FISICA_TOTAL_MM": round(total_sobra, 2),
        "DESPERDICIO_REAL_MM": round(total_desperdicio, 2),
        "DESPERDICIO_MAX_RECOMENDADO_MM": round(
            desperdicio_max_recomendado,
            2,
        ),
        "BARRAS_ACIMA_DESPERDICIO_RECOMENDADO":
            barras_acima_desperdicio_recomendado,
        "MAIOR_DESPERDICIO_POR_BARRA_MM": round(
            maior_desperdicio_por_barra,
            2,
        ),
        "RETALHO_REAPROVEITAVEL_BARRAS":
            retalhos_gerados_barras,
        "RETALHO_REAPROVEITAVEL_MM":
            round(total_retalho, 2),
        "RETALHO_MEDIO_MM":
            metricas_final["RETALHO_MEDIO_MM"],
        "MAIOR_RETALHO_MM":
            metricas_final["MAIOR_RETALHO_MM"],
        "INDICE_CONCENTRACAO_RETALHOS":
            metricas_final["INDICE_CONCENTRACAO"],
        "VALOR_FUTURO_TOTAL":
            metricas_final["VALOR_FUTURO_TOTAL"],
        "APROVEITAMENTO_PERCENTUAL":
            round(aproveitamento_percentual, 2),
        "STATUS": status_texto,
        "PADROES_GERADOS": len(padroes),
    }

    return linhas_plano, resumo, comparacao


def executar_planejado(
    df_demanda,
    tamanho_barra,
    kerf,
    limite_retalho,
    desperdicio_max_recomendado,
    modelo_valor=None,
):
    plano_total = []
    resumos = []
    comparacoes = []

    for diametro in sorted(
        df_demanda["DIAMETRO"].unique()
    ):
        grupo = df_demanda[
            df_demanda["DIAMETRO"] == diametro
        ].copy()

        linhas, resumo, comparacao = otimizar_planejado_por_diametro(
            diametro,
            grupo,
            tamanho_barra,
            kerf,
            limite_retalho,
            desperdicio_max_recomendado,
            modelo_valor=modelo_valor,
        )

        plano_total.extend(linhas)
        resumos.append(resumo)
        comparacoes.extend(comparacao)

    return (
        pd.DataFrame(plano_total),
        pd.DataFrame(resumos),
        pd.DataFrame(comparacoes),
    )


# =====================================================================
# ESTOQUE DINÂMICO / FIFO / ENVELHECIMENTO
# =====================================================================

def simular_estoque_final(
    estoque_inicial,
    plano,
    limite_retalho,
):
    if estoque_inicial is None:
        estoque_inicial = pd.DataFrame()

    estoque = estoque_inicial.copy()

    if estoque.empty:
        estoque = pd.DataFrame(
            columns=[
                "TIPO",
                "DATA_ENTRADA",
                "IDADE_DIAS",
                "DIAMETRO",
                "COMPRIMENTO",
                "QUANTIDADE",
            ]
        )

    if "DATA_ENTRADA" not in estoque.columns:
        estoque["DATA_ENTRADA"] = pd.Timestamp(
            datetime.now().date()
        )

    if "IDADE_DIAS" not in estoque.columns:
        estoque["IDADE_DIAS"] = 0

    movimentos = []

    # Consumo: somente fontes vindas do estoque atual.
    if isinstance(plano, pd.DataFrame) and not plano.empty:
        for _, row in plano.iterrows():
            origem = str(
                row.get("ORIGEM_PLANO", "ESTOQUE_ATUAL")
            )
            tipo = str(
                row.get("TIPO_FONTE", "")
            )

            if origem != "ESTOQUE_ATUAL":
                continue

            diam = float(
                row.get("DIAMETRO", 0) or 0
            )
            comp = float(
                row.get("COMPRIMENTO_FONTE_MM", 0) or 0
            )
            qtd = int(
                row.get("QTD_BARRAS", 1) or 1
            )

            # FIFO por idade: o mais antigo é consumido primeiro.
            candidatos = estoque[
                np.isclose(
                    pd.to_numeric(
                        estoque["DIAMETRO"],
                        errors="coerce",
                    ).fillna(-1).astype(float),
                    diam,
                )
                & np.isclose(
                    pd.to_numeric(
                        estoque["COMPRIMENTO"],
                        errors="coerce",
                    ).fillna(-1).astype(float),
                    comp,
                )
                & (estoque["QUANTIDADE"] > 0)
            ].sort_values(
                "IDADE_DIAS",
                ascending=False,
            )

            restante = qtd

            for idx in candidatos.index:
                if restante <= 0:
                    break

                disponivel = int(
                    estoque.at[idx, "QUANTIDADE"]
                )
                usar = min(
                    disponivel,
                    restante,
                )

                estoque.at[
                    idx,
                    "QUANTIDADE",
                ] = disponivel - usar

                movimentos.append(
                    {
                        "TIPO_MOVIMENTO": "CONSUMO",
                        "DIAMETRO": diam,
                        "COMPRIMENTO": comp,
                        "QUANTIDADE": usar,
                        "TIPO_FONTE": tipo,
                        "DATA": datetime.now().date().isoformat(),
                    }
                )

                restante -= usar

    # Geração de novos retalhos.
    novos = []

    if isinstance(plano, pd.DataFrame) and not plano.empty:
        for _, row in plano.iterrows():
            sobra = float(
                row.get("SOBRA_POR_BARRA_MM", 0) or 0
            )
            qtd = int(
                row.get("QTD_BARRAS", 1) or 1
            )

            if sobra >= limite_retalho and qtd > 0:
                diam = float(
                    row.get("DIAMETRO", 0) or 0
                )

                novos.append(
                    {
                        "TIPO": "RETALHO",
                        "DATA_ENTRADA": pd.Timestamp(
                            datetime.now().date()
                        ),
                        "IDADE_DIAS": 0,
                        "DIAMETRO": diam,
                        "COMPRIMENTO": round(
                            sobra,
                            4,
                        ),
                        "QUANTIDADE": qtd,
                    }
                )

                movimentos.append(
                    {
                        "TIPO_MOVIMENTO": "ENTRADA_RETALHO",
                        "DIAMETRO": diam,
                        "COMPRIMENTO": round(sobra, 4),
                        "QUANTIDADE": qtd,
                        "TIPO_FONTE": "RETALHO_GERADO",
                        "DATA": datetime.now().date().isoformat(),
                    }
                )

    estoque = estoque[
        estoque["QUANTIDADE"] > 0
    ].copy()

    if novos:
        estoque = pd.concat(
            [
                estoque,
                pd.DataFrame(novos),
            ],
            ignore_index=True,
        )

    if not estoque.empty:
        estoque = (
            estoque.groupby(
                [
                    "TIPO",
                    "DATA_ENTRADA",
                    "IDADE_DIAS",
                    "DIAMETRO",
                    "COMPRIMENTO",
                ],
                as_index=False,
            )["QUANTIDADE"]
            .sum()
            .sort_values(
                [
                    "DIAMETRO",
                    "TIPO",
                    "IDADE_DIAS",
                    "COMPRIMENTO",
                ],
                ascending=[
                    True,
                    True,
                    False,
                    False,
                ],
            )
            .reset_index(drop=True)
        )

        estoque["FAIXA_IDADE"] = pd.cut(
            estoque["IDADE_DIAS"],
            bins=[
                -1,
                30,
                60,
                90,
                180,
                10**9,
            ],
            labels=[
                "0-30 dias",
                "31-60 dias",
                "61-90 dias",
                "91-180 dias",
                ">180 dias",
            ],
        ).astype(str)

    return estoque, pd.DataFrame(movimentos)


# =====================================================================
# EXPORTAÇÃO V3
# =====================================================================

def exportar_excel_planejado(
    caminho_demanda,
    plano,
    resumo,
    demanda,
    comparacao=None,
    arquivo_lab=None,
):
    pasta = os.path.dirname(
        caminho_demanda
    )
    timestamp = datetime.now().strftime(
        "%Y%m%d_%H%M%S"
    )
    caminho = os.path.join(
        pasta,
        f"Plano_Corte_Planejado_V3_{timestamp}.xlsx",
    )

    with pd.ExcelWriter(
        caminho,
        engine="openpyxl",
    ) as writer:
        resumo.to_excel(
            writer,
            sheet_name="RESUMO",
            index=False,
        )
        plano.to_excel(
            writer,
            sheet_name="PLANO_DE_CORTE",
            index=False,
        )
        demanda.to_excel(
            writer,
            sheet_name="DEMANDA",
            index=False,
        )

        if (
            isinstance(comparacao, pd.DataFrame)
            and not comparacao.empty
        ):
            comparacao.to_excel(
                writer,
                sheet_name="COMPARACAO_RETALHOS",
                index=False,
            )

        pd.DataFrame(
            [
                {
                    "VERSAO": VERSAO_INDUSTRIAL,
                    "MODELO": (
                        "CSPUL lexicográfico: "
                        "min barras -> min desperdício -> "
                        "min fragmentação -> max valor futuro"
                    ),
                    "ARQUIVO_PRINCIPIA_LAB":
                        arquivo_lab or "NÃO INFORMADO",
                    "BANCO_LOCAL":
                        str(caminho_banco_principia()),
                }
            ]
        ).to_excel(
            writer,
            sheet_name="METODO",
            index=False,
        )

    return caminho


def exportar_excel_emergencial(
    caminho_demanda,
    plano,
    resumo,
    faltas,
    recomendacoes,
    demanda,
    estoque,
    estoque_final=None,
    movimentos=None,
):
    pasta = os.path.dirname(
        caminho_demanda
    )
    timestamp = datetime.now().strftime(
        "%Y%m%d_%H%M%S"
    )
    caminho = os.path.join(
        pasta,
        f"Plano_Corte_Emergencial_V3_{timestamp}.xlsx",
    )

    plano_completo = plano.copy()

    if (
        not plano_completo.empty
        and "ORIGEM_PLANO" not in plano_completo.columns
    ):
        plano_completo["ORIGEM_PLANO"] = "ESTOQUE_ATUAL"

    if not plano_completo.empty:
        plano_estoque = plano_completo[
            plano_completo["ORIGEM_PLANO"]
            == "ESTOQUE_ATUAL"
        ].copy()

        plano_complemento = plano_completo[
            plano_completo["ORIGEM_PLANO"]
            == "COMPLEMENTO_PARA_ATENDER_DEMANDA"
        ].copy()
    else:
        plano_estoque = pd.DataFrame()
        plano_complemento = pd.DataFrame()

    with pd.ExcelWriter(
        caminho,
        engine="openpyxl",
    ) as writer:
        resumo.to_excel(
            writer,
            sheet_name="RESUMO",
            index=False,
        )

        plano_completo.to_excel(
            writer,
            sheet_name="PLANO_COMPLETO",
            index=False,
        )

        (
            plano_estoque
            if not plano_estoque.empty
            else pd.DataFrame(
                [{"STATUS": "NENHUM CORTE COM ESTOQUE ATUAL"}]
            )
        ).to_excel(
            writer,
            sheet_name="CORTE_ESTOQUE",
            index=False,
        )

        (
            plano_complemento
            if not plano_complemento.empty
            else pd.DataFrame(
                [{"STATUS": "SEM COMPLEMENTO NECESSÁRIO"}]
            )
        ).to_excel(
            writer,
            sheet_name="CORTE_COMPLEMENTO",
            index=False,
        )

        demanda.to_excel(
            writer,
            sheet_name="DEMANDA",
            index=False,
        )

        estoque.to_excel(
            writer,
            sheet_name="ESTOQUE_INICIAL",
            index=False,
        )

        if (
            isinstance(estoque_final, pd.DataFrame)
            and not estoque_final.empty
        ):
            estoque_final.to_excel(
                writer,
                sheet_name="ESTOQUE_FINAL",
                index=False,
            )

        if (
            isinstance(movimentos, pd.DataFrame)
            and not movimentos.empty
        ):
            movimentos.to_excel(
                writer,
                sheet_name="MOVIMENTACOES",
                index=False,
            )

        if (
            isinstance(faltas, pd.DataFrame)
            and not faltas.empty
        ):
            faltas.to_excel(
                writer,
                sheet_name="FALTAS",
                index=False,
            )

    return caminho


# =====================================================================
# FOLHA VISUAL / ANIMAÇÃO
# =====================================================================

def _arquivo_para_data_uri(caminho):
    if not caminho or not os.path.exists(caminho):
        return ""

    ext = Path(caminho).suffix.lower().lstrip(".")
    mime = {
        "png": "image/png",
        "jpg": "image/jpeg",
        "jpeg": "image/jpeg",
    }.get(ext)

    if not mime:
        return ""

    dados = base64.b64encode(
        Path(caminho).read_bytes()
    ).decode("ascii")

    return f"data:{mime};base64,{dados}"


def gerar_folha_visual_html(
    plano,
    caminho_excel,
    logo_path=None,
    titulo="Principia Minima - Plano de Corte",
):
    if plano is None or plano.empty:
        return None

    pasta = os.path.dirname(
        caminho_excel
    )
    timestamp = datetime.now().strftime(
        "%Y%m%d_%H%M%S"
    )
    caminho = os.path.join(
        pasta,
        f"Plano_Visual_Corte_{timestamp}.html",
    )

    logo_uri = _arquivo_para_data_uri(
        logo_path
    )

    blocos = []

    for _, row in plano.iterrows():
        fonte = float(
            row.get("COMPRIMENTO_FONTE_MM", 0) or 0
        )
        sobra = float(
            row.get("SOBRA_POR_BARRA_MM", 0) or 0
        )
        cortes = _extrair_cortes_do_esquema(
            row.get("ESQUEMA_DE_CORTE", "")
        )

        segmentos = []

        for comp, qtd in cortes:
            for _ in range(int(qtd)):
                largura = (
                    100.0 * float(comp) / fonte
                    if fonte > 0
                    else 0
                )

                segmentos.append(
                    f"""
                    <div class="peca"
                         style="width:{largura:.5f}%"
                         title="{comp:g} mm">
                        {comp:g}
                    </div>
                    """
                )

        if sobra > 0:
            largura_sobra = (
                100.0 * sobra / fonte
                if fonte > 0
                else 0
            )
            classe = (
                "retalho"
                if "RETALHO" in str(
                    row.get("CLASSIFICACAO_SOBRA", "")
                )
                else "desperdicio"
            )

            segmentos.append(
                f"""
                <div class="{classe}"
                     style="width:{largura_sobra:.5f}%"
                     title="Sobra {sobra:g} mm">
                    {sobra:g}
                </div>
                """
            )

        referencia = html.escape(
            str(
                row.get(
                    "PIV_OFERTA_LINHAS_ATENDIDAS",
                    row.get(
                        "PIV_LINHAS_ATENDIDAS",
                        "",
                    ),
                )
            )
        )

        blocos.append(
            f"""
            <section class="barra-card">
                <div class="barra-titulo">
                    <strong>{html.escape(str(row.get("ID_BARRA", row.get("ID_PADRAO", ""))))}</strong>
                    — Ø{float(row.get("DIAMETRO", 0)):g}
                    — fonte {fonte:g} mm
                </div>
                <div class="barra">{''.join(segmentos)}</div>
                <div class="referencia">{referencia}</div>
            </section>
            """
        )

    logo_html = (
        f'<img class="logo" src="{logo_uri}" alt="MR">'
        if logo_uri
        else '<div class="logo-texto">MR | PRINCIPIA MINIMA</div>'
    )

    documento = f"""<!doctype html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<title>{html.escape(titulo)}</title>
<style>
    * {{ box-sizing: border-box; }}
    body {{
        font-family: Arial, sans-serif;
        margin: 24px;
        color: #1f2937;
        background: white;
    }}
    header {{
        display: flex;
        align-items: center;
        justify-content: space-between;
        border-bottom: 2px solid #1f2937;
        padding-bottom: 12px;
        margin-bottom: 20px;
    }}
    .logo {{ max-height: 54px; max-width: 190px; }}
    .logo-texto {{ font-weight: 700; font-size: 20px; }}
    h1 {{ font-size: 20px; margin: 0; }}
    .meta {{ color: #6b7280; font-size: 12px; margin-top: 4px; }}
    .barra-card {{
        page-break-inside: avoid;
        margin: 14px 0 18px;
    }}
    .barra-titulo {{
        font-size: 12px;
        margin-bottom: 5px;
    }}
    .barra {{
        display: flex;
        height: 42px;
        border: 2px solid #111827;
        overflow: hidden;
        width: 100%;
    }}
    .peca, .retalho, .desperdicio {{
        min-width: 1px;
        border-right: 1px solid #ffffff;
        display: flex;
        align-items: center;
        justify-content: center;
        overflow: hidden;
        font-size: 10px;
        font-weight: 700;
    }}
    .peca {{ background: #2f6db5; color: white; }}
    .retalho {{ background: #dce8c8; color: #1f2937; }}
    .desperdicio {{ background: #d1d5db; color: #374151; }}
    .referencia {{
        font-size: 10px;
        color: #4b5563;
        margin-top: 4px;
    }}
    .legenda {{
        display: flex;
        gap: 18px;
        font-size: 11px;
        margin: 12px 0 18px;
    }}
    .box {{
        width: 12px;
        height: 12px;
        display: inline-block;
        vertical-align: middle;
        margin-right: 4px;
    }}
    @media print {{
        body {{ margin: 10mm; }}
        .nao-imprimir {{ display: none; }}
    }}
</style>
</head>
<body>
<header>
    <div>{logo_html}</div>
    <div>
        <h1>{html.escape(titulo)}</h1>
        <div class="meta">
            Gerado em {datetime.now():%d/%m/%Y %H:%M}
        </div>
    </div>
</header>
<div class="legenda">
    <span><span class="box" style="background:#2f6db5"></span>Peça</span>
    <span><span class="box" style="background:#dce8c8"></span>Retalho reaproveitável</span>
    <span><span class="box" style="background:#d1d5db"></span>Desperdício</span>
</div>
{''.join(blocos)}
</body>
</html>
"""

    Path(caminho).write_text(
        documento,
        encoding="utf-8",
    )

    return caminho


def mostrar_animacao_corte(
    parent,
    plano,
    limite_retalho,
):
    if plano is None or plano.empty:
        messagebox.showwarning(
            "Plano visual",
            "Não há plano de corte disponível.",
        )
        return

    linhas = plano.to_dict(
        orient="records"
    )

    janela = tk.Toplevel(
        parent
    )
    janela.title(
        "Principia Minima - Animação do Corte"
    )
    janela.geometry(
        "1100x720"
    )

    topo = ttk.Frame(
        janela,
        padding=10,
    )
    topo.pack(
        fill="x"
    )

    ttk.Label(
        topo,
        text="PLANO VISUAL DE CORTE",
        style="Titulo.TLabel",
    ).pack(
        side="left"
    )

    canvas_frame = ttk.Frame(
        janela
    )
    canvas_frame.pack(
        fill="both",
        expand=True,
        padx=10,
        pady=5,
    )

    canvas = tk.Canvas(
        canvas_frame,
        background="white",
    )
    scroll = ttk.Scrollbar(
        canvas_frame,
        orient="vertical",
        command=canvas.yview,
    )
    canvas.configure(
        yscrollcommand=scroll.set
    )

    canvas.pack(
        side="left",
        fill="both",
        expand=True,
    )
    scroll.pack(
        side="right",
        fill="y",
    )

    estado = {
        "indice": 0,
        "rodando": False,
    }

    def desenhar_ate(qtd):
        canvas.delete(
            "all"
        )

        y = 30
        largura_total = max(
            780,
            canvas.winfo_width() - 180,
        )
        x0 = 80

        for n, row in enumerate(
            linhas[:qtd]
        ):
            fonte = float(
                row.get(
                    "COMPRIMENTO_FONTE_MM",
                    0,
                )
                or 0
            )
            sobra = float(
                row.get(
                    "SOBRA_POR_BARRA_MM",
                    0,
                )
                or 0
            )

            canvas.create_text(
                20,
                y + 17,
                anchor="w",
                text=(
                    f"{row.get('ID_BARRA', row.get('ID_PADRAO', ''))} "
                    f"| Ø{float(row.get('DIAMETRO', 0)):g}"
                ),
                font=("Arial", 9, "bold"),
            )

            atual_x = x0
            cortes = _extrair_cortes_do_esquema(
                row.get(
                    "ESQUEMA_DE_CORTE",
                    "",
                )
            )

            for comp, qtd_comp in cortes:
                for _ in range(
                    int(qtd_comp)
                ):
                    w = (
                        largura_total * float(comp) / fonte
                        if fonte > 0
                        else 0
                    )
                    canvas.create_rectangle(
                        atual_x,
                        y,
                        atual_x + w,
                        y + 34,
                        fill="#2f6db5",
                        outline="white",
                    )

                    if w >= 35:
                        canvas.create_text(
                            atual_x + w / 2,
                            y + 17,
                            text=f"{comp:g}",
                            fill="white",
                            font=("Arial", 8, "bold"),
                        )

                    atual_x += w

            if sobra > 0:
                w = (
                    largura_total * sobra / fonte
                    if fonte > 0
                    else 0
                )

                cor = (
                    "#dce8c8"
                    if sobra >= limite_retalho
                    else "#d1d5db"
                )

                canvas.create_rectangle(
                    atual_x,
                    y,
                    atual_x + w,
                    y + 34,
                    fill=cor,
                    outline="white",
                )

                if w >= 35:
                    canvas.create_text(
                        atual_x + w / 2,
                        y + 17,
                        text=f"{sobra:g}",
                        fill="#111827",
                        font=("Arial", 8, "bold"),
                    )

                atual_x += w

            canvas.create_rectangle(
                x0,
                y,
                x0 + largura_total,
                y + 34,
                outline="#111827",
                width=2,
            )

            y += 62

        canvas.configure(
            scrollregion=(
                0,
                0,
                x0 + largura_total + 80,
                max(700, y + 40),
            )
        )

    def passo():
        if estado["indice"] < len(linhas):
            estado["indice"] += 1
            desenhar_ate(
                estado["indice"]
            )

        if (
            estado["rodando"]
            and estado["indice"] < len(linhas)
        ):
            janela.after(
                600,
                passo,
            )
        else:
            estado["rodando"] = False

    def reproduzir():
        estado["rodando"] = True
        if estado["indice"] >= len(linhas):
            estado["indice"] = 0
        passo()

    botoes = ttk.Frame(
        janela,
        padding=10,
    )
    botoes.pack(
        fill="x"
    )

    ttk.Button(
        botoes,
        text="Reproduzir",
        command=reproduzir,
    ).pack(
        side="left",
        padx=4,
    )

    ttk.Button(
        botoes,
        text="Próxima barra",
        command=passo,
    ).pack(
        side="left",
        padx=4,
    )

    ttk.Button(
        botoes,
        text="Mostrar tudo",
        command=lambda: desenhar_ate(
            len(linhas)
        ),
    ).pack(
        side="left",
        padx=4,
    )

    desenhar_ate(
        0
    )


# =====================================================================
# INTERFACE INDUSTRIAL V3
# =====================================================================

class PrincipiaMinimaIndustrialApp(PrincipiaMinimaApp):
    def __init__(self):
        self.config_local = carregar_config()
        self.caminho_lab_planejado = self.config_local.get(
            "ultimo_lab",
            "",
        )
        self.logo_path = self.config_local.get(
            "logo_path",
            "",
        )
        self._ultimo_plano = pd.DataFrame()
        self._ultima_comparacao = pd.DataFrame()
        self._ultimo_html = None
        self._ultimo_estoque_final = pd.DataFrame()
        self._ultimo_limite_retalho = LIMITE_RETALHO_DEFAULT

        inicializar_banco()
        super().__init__()

    def _configurar_estilo(self):
        super()._configurar_estilo()
        style = ttk.Style(self)
        style.configure(
            "Cabecalho.TLabel",
            font=("Segoe UI", 24, "bold"),
        )
        style.configure(
            "Secao.TLabelframe.Label",
            font=("Segoe UI", 10, "bold"),
        )

    def _mostrar_logo(self, parent):
        if (
            self.logo_path
            and os.path.exists(self.logo_path)
            and Path(self.logo_path).suffix.lower() == ".png"
        ):
            try:
                imagem = tk.PhotoImage(
                    file=self.logo_path
                )
                label = ttk.Label(
                    parent,
                    image=imagem,
                )
                label.image = imagem
                label.pack(
                    pady=(8, 4)
                )
                return
            except Exception:
                pass

        ttk.Label(
            parent,
            text="MR | PRINCIPIA MINIMA",
            style="Cabecalho.TLabel",
        ).pack(
            pady=(8, 4)
        )

    def selecionar_logo_mr(self):
        caminho = filedialog.askopenfilename(
            title="Selecione o logotipo MR em PNG",
            filetypes=[
                ("PNG", "*.png"),
            ],
        )

        if caminho:
            self.logo_path = caminho
            self.config_local["logo_path"] = caminho
            salvar_config(
                self.config_local
            )
            self.mostrar_inicio()

    def mostrar_inicio(self):
        self.limpar()

        frame = ttk.Frame(
            self,
            padding=36,
        )
        frame.pack(
            expand=True,
            fill="both",
        )

        self._mostrar_logo(
            frame
        )

        ttk.Label(
            frame,
            text=(
                "Sistema industrial de otimização de corte "
                "com retalhos reaproveitáveis"
            ),
            style="Subtitulo.TLabel",
        ).pack(
            pady=(0, 26)
        )

        cards = ttk.Frame(
            frame
        )
        cards.pack(
            expand=True
        )

        emerg = ttk.LabelFrame(
            cards,
            text="EMERGENCIAL",
            padding=25,
            style="Secao.TLabelframe",
        )
        emerg.grid(
            row=0,
            column=0,
            padx=12,
            pady=10,
            sticky="nsew",
        )

        ttk.Label(
            emerg,
            text=(
                "Estoque atual + demanda semanal\n\n"
                "Controla barras, retalhos e saldo final."
            ),
            justify="center",
        ).pack(
            pady=10
        )

        ttk.Button(
            emerg,
            text="ABRIR EMERGENCIAL",
            style="Acao.TButton",
            command=self.mostrar_emergencial,
        ).pack(
            pady=12
        )

        planej = ttk.LabelFrame(
            cards,
            text="PLANEJADO INTELIGENTE",
            padding=25,
            style="Secao.TLabelframe",
        )
        planej.grid(
            row=0,
            column=1,
            padx=12,
            pady=10,
            sticky="nsew",
        )

        ttk.Label(
            planej,
            text=(
                "Demanda futura + Principia Lab\n\n"
                "Barras → desperdício → fragmentação → valor futuro."
            ),
            justify="center",
        ).pack(
            pady=10
        )

        ttk.Button(
            planej,
            text="ABRIR PLANEJADO",
            style="Acao.TButton",
            command=self.mostrar_planejado,
        ).pack(
            pady=12
        )

        apoio = ttk.LabelFrame(
            frame,
            text="                   Ferramentas",
            padding=12,
        )
        apoio.pack(
            pady=18
        )

        ttk.Button(
            apoio,
            text="Histórico de otimizações",
            command=self.mostrar_historico,
        ).pack(
            side="left",
            padx=5,
        )

        ttk.Label(
            frame,
            text=(
                f"Versão {VERSAO_INDUSTRIAL}  "
            ),
            foreground="gray",
        ).pack(
            side="bottom",
            pady=10,
        )

    def mostrar_historico(self):
        df = ler_historico_execucoes(
            200
        )

        janela = tk.Toplevel(
            self
        )
        janela.title(
            "Histórico - Principia Minima"
        )
        janela.geometry(
            "1100x520"
        )

        colunas = (
            "data_hora",
            "modo",
            "horizonte_lab",
            "arquivo_demanda",
            "excel_saida",
        )

        tree = ttk.Treeview(
            janela,
            columns=colunas,
            show="headings",
        )

        nomes = {
            "data_hora": "Data/Hora",
            "modo": "Modo",
            "horizonte_lab": "Horizonte",
            "arquivo_demanda": "Demanda",
            "excel_saida": "Saída",
        }

        for c in colunas:
            tree.heading(
                c,
                text=nomes[c],
            )
            tree.column(
                c,
                width=180 if c != "excel_saida" else 340,
            )

        for _, row in df.iterrows():
            tree.insert(
                "",
                "end",
                values=tuple(
                    row.get(c, "")
                    for c in colunas
                ),
            )

        scroll = ttk.Scrollbar(
            janela,
            orient="vertical",
            command=tree.yview,
        )
        tree.configure(
            yscrollcommand=scroll.set
        )

        tree.pack(
            side="left",
            fill="both",
            expand=True,
            padx=(10, 0),
            pady=10,
        )
        scroll.pack(
            side="right",
            fill="y",
            padx=(0, 10),
            pady=10,
        )

    # -------------------------------------------------------------
    # PLANEJADO V3
    # -------------------------------------------------------------
    def mostrar_planejado(self):
        self.limpar()
        self.caminho_demanda_planejado = None

        frame = ttk.Frame(
            self,
            padding=25,
        )
        frame.pack(
            fill="both",
            expand=True,
        )

        ttk.Button(
            frame,
            text="< Voltar",
            command=self.mostrar_inicio,
        ).pack(
            anchor="w"
        )

        ttk.Label(
            frame,
            text="PLANEJAMENTO INTELIGENTE",
            style="Titulo.TLabel",
        ).pack(
            pady=(12, 5)
        )

        ttk.Label(
            frame,
            text=(
                "Modelo CSPUL lexicográfico com referência histórica "
                "do Principia Lab."
            ),
        ).pack(
            pady=(0, 16)
        )

        entrada = ttk.LabelFrame(
            frame,
            text="Parâmetros físicos",
            padding=14,
        )
        entrada.pack(
            fill="x",
            pady=8,
        )

        ttk.Label(
            entrada,
            text="Barra padrão (mm)",
        ).grid(
            row=0,
            column=0,
            padx=8,
            pady=4,
        )
        self.entry_barra_p = ttk.Entry(
            entrada,
            width=15,
        )
        self.entry_barra_p.insert(
            0,
            str(BARRA_PADRAO_DEFAULT),
        )
        self.entry_barra_p.grid(
            row=1,
            column=0,
            padx=8,
        )

        ttk.Label(
            entrada,
            text="Kerf (mm)",
        ).grid(
            row=0,
            column=1,
            padx=8,
            pady=4,
        )
        self.entry_kerf_p = ttk.Entry(
            entrada,
            width=15,
        )
        self.entry_kerf_p.insert(
            0,
            str(KERF_DEFAULT),
        )
        self.entry_kerf_p.grid(
            row=1,
            column=1,
            padx=8,
        )

        ttk.Label(
            entrada,
            text="Limite retalho (mm)",
        ).grid(
            row=0,
            column=2,
            padx=8,
            pady=4,
        )
        self.entry_retalho_p = ttk.Entry(
            entrada,
            width=15,
        )
        self.entry_retalho_p.insert(
            0,
            str(LIMITE_RETALHO_DEFAULT),
        )
        self.entry_retalho_p.grid(
            row=1,
            column=2,
            padx=8,
        )

        ttk.Label(
            entrada,
            text="Desperdício máx. recomendado (mm)",
        ).grid(
            row=0,
            column=3,
            padx=8,
            pady=4,
        )
        self.entry_desperdicio_max_p = ttk.Entry(
            entrada,
            width=22,
        )
        self.entry_desperdicio_max_p.insert(
            0,
            str(DESPERDICIO_MAX_RECOMENDADO_DEFAULT),
        )
        self.entry_desperdicio_max_p.grid(
            row=1,
            column=3,
            padx=8,
        )

        arquivos = ttk.LabelFrame(
            frame,
            text="Demanda",
            padding=14,
        )
        arquivos.pack(
            fill="x",
            pady=8,
        )

        ttk.Button(
            arquivos,
            text="Selecionar demanda (.csv/.xlsx)",
            command=self.selecionar_demanda_planejado,
        ).grid(
            row=0,
            column=0,
            sticky="w",
            padx=4,
            pady=4,
        )

        self.label_demanda_p = ttk.Label(
            arquivos,
            text="Nenhum arquivo selecionado.",
        )
        self.label_demanda_p.grid(
            row=0,
            column=1,
            sticky="w",
            padx=10,
        )

        lab = ttk.LabelFrame(
            frame,
            text="Inteligência histórica - Principia Lab",
            padding=14,
        )
        lab.pack(
            fill="x",
            pady=8,
        )

        ttk.Button(
            lab,
            text="Selecionar Principia_Lab_resultados.xlsx",
            command=self.selecionar_lab_planejado,
        ).grid(
            row=0,
            column=0,
            padx=4,
            pady=4,
            sticky="w",
        )

        self.label_lab_p = ttk.Label(
            lab,
            text=(
                os.path.basename(self.caminho_lab_planejado)
                if self.caminho_lab_planejado
                else "Sem Lab: será usado fallback por concentração"
            ),
        )
        self.label_lab_p.grid(
            row=0,
            column=1,
            padx=10,
            sticky="w",
        )

        ttk.Label(
            lab,
            text="Horizonte de valor:",
        ).grid(
            row=1,
            column=0,
            padx=4,
            pady=6,
            sticky="w",
        )

        self.combo_horizonte_p = ttk.Combobox(
            lab,
            state="readonly",
            values=list(
                HORIZONTES_LAB.keys()
            ),
            width=22,
        )
        self.combo_horizonte_p.set(
            "Média 15/30/60"
        )
        self.combo_horizonte_p.grid(
            row=1,
            column=1,
            padx=10,
            pady=6,
            sticky="w",
        )

        ttk.Label(
            lab,
            text=(
                "Sem arquivo do Lab, a Etapa 4 usa soma dos quadrados "
                "das sobras como critério de concentração."
            ),
            foreground="gray",
        ).grid(
            row=2,
            column=0,
            columnspan=2,
            sticky="w",
            padx=4,
        )

        ttk.Button(
            frame,
            text="OTIMIZAR + GERAR PLANO VISUAL",
            style="Acao.TButton",
            command=self.processar_planejado,
        ).pack(
            pady=24
        )

    def selecionar_demanda_planejado(self):
        caminho = filedialog.askopenfilename(
            title="Selecione a demanda futura",
            filetypes=[
                ("Planilhas", "*.xlsx *.xlsm *.xls *.csv"),
                ("Excel", "*.xlsx *.xlsm *.xls"),
                ("CSV", "*.csv"),
            ],
        )

        if caminho:
            self.caminho_demanda_planejado = caminho
            self.label_demanda_p.config(
                text=os.path.basename(caminho)
            )

    def selecionar_lab_planejado(self):
        caminho = filedialog.askopenfilename(
            title="Selecione os resultados do Principia Lab",
            filetypes=[
                ("Excel", "*.xlsx"),
            ],
        )

        if caminho:
            try:
                teste = ModeloValorRetalho(
                    caminho,
                    "MEDIA",
                )

                if not teste.disponivel:
                    raise ValueError(
                        "Nenhum dado de valor encontrado."
                    )

                self.caminho_lab_planejado = caminho
                self.config_local["ultimo_lab"] = caminho
                salvar_config(
                    self.config_local
                )
                self.label_lab_p.config(
                    text=os.path.basename(caminho)
                )

            except Exception as erro:
                messagebox.showerror(
                    "Principia Lab",
                    str(erro),
                )

    def processar_planejado(self):
        if not self.caminho_demanda_planejado:
            messagebox.showwarning(
                "Demanda",
                "Selecione a planilha de demanda.",
            )
            return

        try:
            tamanho_barra = float(
                self.entry_barra_p.get().replace(",", ".")
            )
            kerf = float(
                self.entry_kerf_p.get().replace(",", ".")
            )
            limite = float(
                self.entry_retalho_p.get().replace(",", ".")
            )
            desperdicio_max = float(
                self.entry_desperdicio_max_p.get().replace(",", ".")
            )

            if (
                tamanho_barra <= 0
                or kerf < 0
                or limite < 0
                or desperdicio_max < 0
            ):
                raise ValueError(
                    "Parâmetros físicos inválidos."
                )

            df_detalhada = ler_demanda_csv(
                self.caminho_demanda_planejado
            )
            df_solver = agrupar_demanda_para_solver(
                df_detalhada
            )

            horizonte_nome = self.combo_horizonte_p.get()
            horizonte = HORIZONTES_LAB.get(
                horizonte_nome,
                "MEDIA",
            )

            modelo = None

            if (
                self.caminho_lab_planejado
                and os.path.exists(
                    self.caminho_lab_planejado
                )
            ):
                modelo = ModeloValorRetalho(
                    self.caminho_lab_planejado,
                    horizonte,
                )

            plano, resumo, comparacao = executar_planejado(
                df_solver,
                tamanho_barra,
                kerf,
                limite,
                desperdicio_max,
                modelo_valor=modelo,
            )

            plano = adicionar_rastreabilidade_ao_plano(
                plano,
                df_detalhada,
            )

            plano = anotar_valor_retalhos(
                plano,
                modelo,
                limite,
                horizonte,
            )

            excel = exportar_excel_planejado(
                self.caminho_demanda_planejado,
                plano,
                resumo,
                df_detalhada.drop(
                    columns=["_ORDEM"],
                    errors="ignore",
                ),
                comparacao=comparacao,
                arquivo_lab=self.caminho_lab_planejado,
            )

            visual = gerar_folha_visual_html(
                plano,
                excel,
                logo_path=self.logo_path,
                titulo="Principia Minima - Planejamento de Corte",
            )

            self._ultimo_plano = plano
            self._ultima_comparacao = comparacao
            self._ultimo_html = visual
            self._ultimo_estoque_final = pd.DataFrame()
            self._ultimo_limite_retalho = limite

            self._ultima_execucao_id = registrar_execucao_historico(
                modo="PLANEJADO",
                arquivo_demanda=self.caminho_demanda_planejado,
                resumo=resumo,
                plano=plano,
                excel_saida=excel,
                folha_visual=visual,
                arquivo_lab=self.caminho_lab_planejado,
                horizonte_lab=horizonte,
                parametros={
                    "barra_padrao": tamanho_barra,
                    "kerf": kerf,
                    "limite_retalho": limite,
                    "desperdicio_max": desperdicio_max,
                },
            )

            self.mostrar_resultado(
                "PLANEJADO",
                resumo,
                excel,
                pd.DataFrame(),
            )

        except Exception as erro:
            messagebox.showerror(
                "Erro de Processamento",
                str(erro),
            )

    # -------------------------------------------------------------
    # EMERGENCIAL V3
    # -------------------------------------------------------------
    def selecionar_demanda_emergencial(self):
        caminho = filedialog.askopenfilename(
            title="Selecione a demanda semanal",
            filetypes=[
                ("Planilhas", "*.xlsx *.xlsm *.xls *.csv"),
                ("Excel", "*.xlsx *.xlsm *.xls"),
                ("CSV", "*.csv"),
            ],
        )

        if caminho:
            self.caminho_demanda_emergencial = caminho
            self.label_demanda_e.config(
                text=os.path.basename(caminho)
            )

    def selecionar_estoque_emergencial(self):
        caminho = filedialog.askopenfilename(
            title="Selecione o estoque atual",
            filetypes=[
                ("Planilhas", "*.xlsx *.xlsm *.xls *.csv"),
                ("Excel", "*.xlsx *.xlsm *.xls"),
                ("CSV", "*.csv"),
            ],
        )

        if caminho:
            self.caminho_estoque_emergencial = caminho
            self.label_estoque_e.config(
                text=os.path.basename(caminho)
            )

    def obter_estoque_emergencial(self, barra_padrao):
        dataframes = []

        if self.caminho_estoque_emergencial:
            dataframes.append(
                ler_estoque_csv(
                    self.caminho_estoque_emergencial,
                    barra_padrao,
                )
            )

        registros_manuais = []

        for item in self.tabela_estoque_e.get_children():
            valores = self.tabela_estoque_e.item(
                item,
                "values",
            )

            diametro = float(
                str(valores[0]).replace(",", ".")
            )
            comprimento = float(
                str(valores[1]).replace(",", ".")
            )
            quantidade = int(
                valores[2]
            )

            tipo = (
                "NOVA"
                if abs(
                    comprimento - barra_padrao
                ) <= 1e-6
                else "RETALHO"
            )

            registros_manuais.append(
                {
                    "TIPO": tipo,
                    "DATA_ENTRADA": pd.Timestamp(
                        datetime.now().date()
                    ),
                    "IDADE_DIAS": 0,
                    "DIAMETRO": round(diametro, 4),
                    "COMPRIMENTO": round(comprimento, 4),
                    "QUANTIDADE": quantidade,
                }
            )

        if registros_manuais:
            dataframes.append(
                pd.DataFrame(
                    registros_manuais
                )
            )

        if not dataframes:
            raise ValueError(
                "Informe estoque manualmente ou selecione uma planilha."
            )

        df = pd.concat(
            dataframes,
            ignore_index=True,
        )

        if "DATA_ENTRADA" not in df.columns:
            df["DATA_ENTRADA"] = pd.Timestamp(
                datetime.now().date()
            )

        if "IDADE_DIAS" not in df.columns:
            df["IDADE_DIAS"] = 0

        return (
            df.groupby(
                [
                    "TIPO",
                    "DATA_ENTRADA",
                    "IDADE_DIAS",
                    "DIAMETRO",
                    "COMPRIMENTO",
                ],
                as_index=False,
            )["QUANTIDADE"]
            .sum()
            .sort_values(
                [
                    "DIAMETRO",
                    "TIPO",
                    "IDADE_DIAS",
                    "COMPRIMENTO",
                ],
                ascending=[
                    True,
                    True,
                    False,
                    False,
                ],
            )
            .reset_index(drop=True)
        )

    def processar_emergencial(self):
        if not self.caminho_demanda_emergencial:
            messagebox.showwarning(
                "Demanda",
                "Selecione a planilha de demanda semanal.",
            )
            return

        try:
            kerf = float(
                self.entry_kerf_e.get().replace(",", ".")
            )
            limite = float(
                self.entry_retalho_e.get().replace(",", ".")
            )
            barra_padrao = float(
                self.entry_barra_e.get().replace(",", ".")
            )
            desperdicio_max = float(
                self.entry_desperdicio_max_e.get().replace(",", ".")
            )

            df_detalhada = ler_demanda_csv(
                self.caminho_demanda_emergencial
            )
            df_solver = agrupar_demanda_para_solver(
                df_detalhada
            )
            estoque = self.obter_estoque_emergencial(
                barra_padrao
            )

            plano, resumo, faltas, recomendacoes = executar_emergencial(
                df_solver,
                estoque,
                kerf,
                limite,
                desperdicio_max,
                barra_padrao,
            )

            plano = adicionar_rastreabilidade_ao_plano(
                plano,
                df_detalhada,
            )

            # O emergencial também recebe a leitura V(r,phi), se o último
            # arquivo do Lab continuar disponível.
            modelo = None

            if (
                self.caminho_lab_planejado
                and os.path.exists(
                    self.caminho_lab_planejado
                )
            ):
                try:
                    modelo = ModeloValorRetalho(
                        self.caminho_lab_planejado,
                        "MEDIA",
                    )
                except Exception:
                    modelo = None

            plano = anotar_valor_retalhos(
                plano,
                modelo,
                limite,
                "MEDIA",
            )

            estoque_final, movimentos = simular_estoque_final(
                estoque,
                plano,
                limite,
            )

            excel = exportar_excel_emergencial(
                self.caminho_demanda_emergencial,
                plano,
                resumo,
                faltas,
                recomendacoes,
                df_detalhada.drop(
                    columns=["_ORDEM"],
                    errors="ignore",
                ),
                estoque,
                estoque_final=estoque_final,
                movimentos=movimentos,
            )

            visual = gerar_folha_visual_html(
                plano,
                excel,
                logo_path=self.logo_path,
                titulo="Principia Minima - Corte Emergencial",
            )

            self._ultimo_plano = plano
            self._ultima_comparacao = pd.DataFrame()
            self._ultimo_html = visual
            self._ultimo_estoque_final = estoque_final
            self._ultimo_limite_retalho = limite

            self._ultima_execucao_id = registrar_execucao_historico(
                modo="EMERGENCIAL",
                arquivo_demanda=self.caminho_demanda_emergencial,
                arquivo_estoque=self.caminho_estoque_emergencial,
                resumo=resumo,
                plano=plano,
                excel_saida=excel,
                folha_visual=visual,
                arquivo_lab=self.caminho_lab_planejado,
                horizonte_lab="MEDIA",
                parametros={
                    "barra_padrao": barra_padrao,
                    "kerf": kerf,
                    "limite_retalho": limite,
                    "desperdicio_max": desperdicio_max,
                },
                estoque_inicial=estoque,
                estoque_final=estoque_final,
            )

            self.mostrar_resultado(
                "EMERGENCIAL",
                resumo,
                excel,
                faltas,
            )

        except Exception as erro:
            messagebox.showerror(
                "Erro de Processamento",
                str(erro),
            )

    # -------------------------------------------------------------
    # RESULTADO V3
    # -------------------------------------------------------------
    def mostrar_resultado(
        self,
        modo,
        resumo,
        caminho_excel,
        faltas,
    ):
        janela = tk.Toplevel(
            self
        )
        janela.title(
            f"Resultado - {modo}"
        )
        janela.geometry(
            "980x650"
        )

        ttk.Label(
            janela,
            text=f"RESULTADO - {modo}",
            style="Titulo.TLabel",
        ).pack(
            pady=(18, 8)
        )

        if (
            modo == "PLANEJADO"
            and isinstance(
                self._ultima_comparacao,
                pd.DataFrame,
            )
            and not self._ultima_comparacao.empty
        ):
            comparacao_box = ttk.LabelFrame(
                janela,
                text="Comparação dos conjuntos de retalhos",
                padding=8,
            )
            comparacao_box.pack(
                fill="x",
                padx=18,
                pady=5,
            )

            for diam in sorted(
                self._ultima_comparacao["DIAMETRO"].unique()
            ):
                g = self._ultima_comparacao[
                    self._ultima_comparacao["DIAMETRO"] == diam
                ]

                base = g[
                    g["CENARIO"] == "BASE_MIN_DESPERDICIO"
                ]
                intel = g[
                    g["CENARIO"] == "PLANO_INTELIGENTE"
                ]

                if base.empty or intel.empty:
                    continue

                b = base.iloc[0]
                i = intel.iloc[0]

                texto_cmp = (
                    f"Ø{diam:g}: retalhos {int(b['QTD_RETALHOS_REAPROVEITAVEIS'])} → "
                    f"{int(i['QTD_RETALHOS_REAPROVEITAVEIS'])} | "
                    f"maior retalho {b['MAIOR_RETALHO_MM']:.0f} → "
                    f"{i['MAIOR_RETALHO_MM']:.0f} mm | "
                    f"valor futuro {b['VALOR_FUTURO_TOTAL']:.1f} → "
                    f"{i['VALOR_FUTURO_TOTAL']:.1f}"
                )

                ttk.Label(
                    comparacao_box,
                    text=texto_cmp,
                ).pack(
                    anchor="w"
                )

        texto = tk.Text(
            janela,
            height=22,
            width=110,
            font=("Consolas", 10),
        )
        texto.pack(
            fill="both",
            expand=True,
            padx=18,
            pady=10,
        )

        for _, row in resumo.iterrows():
            texto.insert(
                "end",
                f"DIÂMETRO: {row['DIAMETRO']:g}\n",
            )
            texto.insert(
                "end",
                f"  Barras novas usadas: {int(row.get('BARRAS_NOVAS_USADAS', 0))}\n",
            )
            texto.insert(
                "end",
                f"  Desperdício real: {float(row.get('DESPERDICIO_REAL_MM', 0)):.2f} mm\n",
            )
            texto.insert(
                "end",
                f"  Retalho reaproveitável: "
                f"{float(row.get('RETALHO_REAPROVEITAVEL_MM', 0)):.2f} mm\n",
            )

            if "RETALHO_MEDIO_MM" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Retalho médio: {float(row.get('RETALHO_MEDIO_MM', 0)):.2f} mm\n",
                )

            if "MAIOR_RETALHO_MM" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Maior retalho: {float(row.get('MAIOR_RETALHO_MM', 0)):.2f} mm\n",
                )

            if "VALOR_FUTURO_TOTAL" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Valor futuro do conjunto: "
                    f"{float(row.get('VALOR_FUTURO_TOTAL', 0)):.2f}\n",
                )

            if "APROVEITAMENTO_PERCENTUAL" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Aproveitamento: "
                    f"{float(row.get('APROVEITAMENTO_PERCENTUAL', 0)):.2f}%\n",
                )

            if "PECAS_FALTANTES" in resumo.columns:
                texto.insert(
                    "end",
                    f"  Peças faltantes: "
                    f"{int(row.get('PECAS_FALTANTES', 0))}\n",
                )

            texto.insert(
                "end",
                f"  Status: {row.get('STATUS', '')}\n",
            )
            texto.insert(
                "end",
                "-" * 78 + "\n",
            )

        texto.insert(
            "end",
            f"\nExcel:\n{caminho_excel}\n",
        )

        if self._ultimo_html:
            texto.insert(
                "end",
                f"\nFolha visual:\n{self._ultimo_html}\n",
            )

        texto.config(
            state="disabled"
        )

        botoes = ttk.Frame(
            janela
        )
        botoes.pack(
            pady=(0, 15)
        )

        ttk.Button(
            botoes,
            text="Abrir Excel",
            command=lambda: self.abrir_arquivo(
                caminho_excel
            ),
        ).pack(
            side="left",
            padx=4,
        )

        ttk.Button(
            botoes,
            text="Plano visual",
            command=lambda: mostrar_animacao_corte(
                self,
                self._ultimo_plano,
                self._ultimo_limite_retalho,
            ),
        ).pack(
            side="left",
            padx=4,
        )

        if self._ultimo_html:
            ttk.Button(
                botoes,
                text="Folha para imprimir",
                command=lambda: webbrowser.open(
                    Path(
                        self._ultimo_html
                    ).resolve().as_uri()
                ),
            ).pack(
                side="left",
                padx=4,
            )

        ttk.Button(
            botoes,
            text="Abrir pasta",
            command=lambda: self.abrir_pasta(
                os.path.dirname(
                    caminho_excel
                )
            ),
        ).pack(
            side="left",
            padx=4,
        )

        ttk.Button(
            botoes,
            text="Fechar",
            command=janela.destroy,
        ).pack(
            side="left",
            padx=4,
        )


# =====================================================================
# PRINCIPIA MINIMA V3.1 - INTERFACE MODERNA
# Baseado diretamente no arquivo principal V3.0 Industrial.
# A lógica matemática, parâmetros físicos e parâmetros de planejamento
# permanecem inalterados. Esta camada modifica a experiência visual,
# adiciona progresso/ETA e um dashboard final no estilo corporativo.
# =====================================================================
import threading
import queue

EMBEDDED_MR_LOGO_PNG_B64 = """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"""


class ProgressoSolverDialog(tk.Toplevel):
    """Janela de progresso com percentual e ETA estimado.

    O ETA é uma estimativa operacional: usa o orçamento máximo de solver
    (60 s por diâmetro) e é recalculado conforme as etapas terminam.
    """

    def __init__(self, parent, titulo, colors):
        super().__init__(parent)
        self.parent = parent
        self.colors = colors
        self.stage_start_time = None
        self.stage_end_time = None
        self.stage_from = 0.0
        self.stage_to = 0.0
        self.manual_percent = 0.0

        self.percent_var = tk.DoubleVar(value=0.0)
        self.percent_text = tk.StringVar(value='0%')
        self.status_var = tk.StringVar(value='Preparando processamento...')
        self.eta_var = tk.StringVar(value='Tempo restante estimado: --')

        self.title(titulo)
        self.geometry('600x270')
        self.resizable(False, False)
        self.configure(bg=colors['background'])
        self.transient(parent)
        self.grab_set()
        self.protocol('WM_DELETE_WINDOW', lambda: None)

        outer = tk.Frame(self, bg=colors['background'], padx=20, pady=18)
        outer.pack(fill='both', expand=True)

        card = tk.Frame(
            outer,
            bg=colors['white'],
            highlightbackground=colors['border'],
            highlightthickness=1,
            bd=0,
        )
        card.pack(fill='both', expand=True)

        header = tk.Frame(card, bg=colors['navy'], height=58)
        header.pack(fill='x')
        header.pack_propagate(False)
        tk.Label(
            header,
            text=titulo,
            bg=colors['navy'],
            fg=colors['white'],
            font=('Segoe UI', 14, 'bold'),
        ).pack(side='left', padx=18)

        body = tk.Frame(card, bg=colors['white'], padx=18, pady=16)
        body.pack(fill='both', expand=True)

        tk.Label(
            body,
            textvariable=self.status_var,
            bg=colors['white'],
            fg=colors['text'],
            font=('Segoe UI', 11, 'bold'),
            anchor='w',
        ).pack(fill='x')

        self.bar = ttk.Progressbar(
            body,
            maximum=100,
            variable=self.percent_var,
            style='Overall.Horizontal.TProgressbar',
        )
        self.bar.pack(fill='x', pady=(14, 10))

        stats = tk.Frame(body, bg=colors['white'])
        stats.pack(fill='x')
        tk.Label(
            stats,
            textvariable=self.percent_text,
            bg=colors['white'],
            fg=colors['blue'],
            font=('Segoe UI', 22, 'bold'),
        ).pack(side='left')
        tk.Label(
            stats,
            textvariable=self.eta_var,
            bg=colors['white'],
            fg=colors['muted'],
            font=('Segoe UI', 10),
        ).pack(side='right')

        tk.Label(
            body,
            text=(
                'O tempo restante é estimado a partir do limite de otimização '
                'e é atualizado conforme cada diâmetro é concluído.'
            ),
            bg=colors['white'],
            fg=colors['muted'],
            font=('Segoe UI', 9),
            wraplength=530,
            justify='left',
        ).pack(fill='x', pady=(12, 0))

        self.after(200, self._tick)
        self.after(10, self._center)

    def _center(self):
        self.update_idletasks()
        try:
            pw = self.parent.winfo_width()
            ph = self.parent.winfo_height()
            px = self.parent.winfo_rootx()
            py = self.parent.winfo_rooty()
            w = self.winfo_width()
            h = self.winfo_height()
            self.geometry(f'{w}x{h}+{px + max((pw-w)//2, 0)}+{py + max((ph-h)//2, 0)}')
        except Exception:
            pass

    def set_stage(self, percent_from, percent_to, message, eta_seconds=None):
        self.stage_from = max(0.0, min(100.0, float(percent_from)))
        self.stage_to = max(self.stage_from, min(100.0, float(percent_to)))
        self.manual_percent = self.stage_from
        self.status_var.set(message)
        self.percent_var.set(self.stage_from)
        self.percent_text.set(f'{self.stage_from:.0f}%')
        self.stage_start_time = time.time()
        self.stage_end_time = (
            self.stage_start_time + max(float(eta_seconds), 0.0)
            if eta_seconds is not None else None
        )
        self.update_idletasks()

    def set_exact(self, percent, message=None, eta_seconds=None):
        p = max(0.0, min(100.0, float(percent)))
        self.stage_from = p
        self.stage_to = p
        self.manual_percent = p
        self.stage_start_time = time.time()
        self.stage_end_time = (
            self.stage_start_time + max(float(eta_seconds), 0.0)
            if eta_seconds is not None else None
        )
        if message is not None:
            self.status_var.set(message)
        self.percent_var.set(p)
        self.percent_text.set(f'{p:.0f}%')
        self.update_idletasks()

    def finish(self):
        self.set_exact(100, 'Processamento concluído. Abrindo dashboard...', 0)
        self.eta_var.set('Tempo restante estimado: 0s')

    def _tick(self):
        if not self.winfo_exists():
            return
        now = time.time()
        percent = self.manual_percent
        eta = None

        if self.stage_start_time is not None and self.stage_end_time is not None:
            total = max(self.stage_end_time - self.stage_start_time, 0.001)
            elapsed = max(now - self.stage_start_time, 0.0)
            frac = min(elapsed / total, 0.96)
            if self.stage_to > self.stage_from:
                percent = self.stage_from + (self.stage_to - self.stage_from) * frac
            eta = max(int(round(self.stage_end_time - now)), 0)
        elif self.percent_var.get() >= 100:
            eta = 0

        self.percent_var.set(percent)
        self.percent_text.set(f'{percent:.0f}%')

        if eta is None:
            self.eta_var.set('Tempo restante estimado: --')
        else:
            mins, secs = divmod(eta, 60)
            if mins:
                self.eta_var.set(f'Tempo restante estimado: {mins}min {secs:02d}s')
            else:
                self.eta_var.set(f'Tempo restante estimado: {secs}s')

        self.after(200, self._tick)


class PrincipiaMinimaModernApp(PrincipiaMinimaIndustrialApp):
    COLORS = {
        'navy': '#17365D',
        'blue': '#1F4E78',
        'light_blue': '#D9EAF7',
        'green': '#70AD47',
        'green_light': '#E2F0D9',
        'amber': '#D6A100',
        'amber_light': '#FFF2CC',
        'gray': '#A5A5A5',
        'gray_light': '#E7E6E6',
        'white': '#FFFFFF',
        'background': '#F3F6F9',
        'text': '#1F2937',
        'muted': '#5B6573',
        'border': '#DDE5EC',
        'danger': '#B94A48',
    }

    def __init__(self):
        self._embedded_logo = None
        super().__init__()
        self.title('Principia Minima - Otimização de Corte')
        self.configure(bg=self.COLORS['background'])
        self.minsize(1180, 720)
        # Materializa a logo incorporada numa pasta local para que ela também
        # possa aparecer na folha HTML impressa, sem depender de arquivo externo.
        self.logo_path = self._ensure_embedded_logo_file()

    # -----------------------------------------------------------------
    # VISUAL CORPORATIVO - inspirado no Controle de Expedição
    # -----------------------------------------------------------------
    def _configurar_estilo(self):
        style = ttk.Style(self)
        if 'clam' in style.theme_names():
            style.theme_use('clam')

        c = self.COLORS

        style.configure('TFrame', background=c['background'])
        style.configure('TLabel', background=c['background'], foreground=c['text'])
        style.configure('White.TLabel', background=c['white'], foreground=c['text'])
        style.configure('MutedWhite.TLabel', background=c['white'], foreground=c['muted'], font=('Segoe UI', 9))
        style.configure('Section.TLabel', background=c['background'], foreground=c['navy'], font=('Segoe UI', 12, 'bold'))
        style.configure('Titulo.TLabel', background=c['background'], foreground=c['navy'], font=('Segoe UI', 20, 'bold'))
        style.configure('Subtitulo.TLabel', background=c['background'], foreground=c['muted'], font=('Segoe UI', 10))
        style.configure('HeroTitle.TLabel', background=c['navy'], foreground=c['white'], font=('Segoe UI', 20, 'bold'))
        style.configure('HeroSub.TLabel', background=c['navy'], foreground=c['light_blue'], font=('Segoe UI', 10))
        style.configure('Card.TFrame', background=c['white'], relief='solid', borderwidth=1)
        style.configure('CardTitle.TLabel', background=c['white'], foreground=c['muted'], font=('Segoe UI', 9, 'bold'))
        style.configure('CardValue.TLabel', background=c['white'], foreground=c['navy'], font=('Segoe UI', 22, 'bold'))
        style.configure('Card.TLabelframe', background=c['white'], borderwidth=1, relief='solid')
        style.configure('Card.TLabelframe.Label', background=c['white'], foreground=c['navy'], font=('Segoe UI', 10, 'bold'))
        style.configure('TNotebook', background=c['background'], borderwidth=0)
        style.configure('TNotebook.Tab', padding=(18, 9), font=('Segoe UI', 10, 'bold'))
        style.map('TNotebook.Tab', background=[('selected', c['white']), ('active', c['light_blue'])])
        style.configure('Treeview', rowheight=31, font=('Segoe UI', 9), background=c['white'], fieldbackground=c['white'])
        style.configure('Treeview.Heading', background=c['blue'], foreground=c['white'], font=('Segoe UI', 9, 'bold'), padding=(6, 8))
        style.map('Treeview.Heading', background=[('active', c['navy'])])
        style.configure('Accent.TButton', font=('Segoe UI', 9, 'bold'), padding=(13, 8), background=c['blue'], foreground=c['white'])
        style.map('Accent.TButton', background=[('active', c['navy']), ('pressed', c['navy'])])
        style.configure('Secondary.TButton', font=('Segoe UI', 9, 'bold'), padding=(12, 8), background=c['white'], foreground=c['navy'])
        style.map('Secondary.TButton', background=[('active', c['light_blue'])])
        style.configure('Acao.TButton', font=('Segoe UI', 10, 'bold'), padding=(14, 10), background=c['blue'], foreground=c['white'])
        style.map('Acao.TButton', background=[('active', c['navy']), ('pressed', c['navy'])])
        style.configure('Overall.Horizontal.TProgressbar', troughcolor='#DDE5EC', background=c['blue'], thickness=18)

    def _ensure_embedded_logo_file(self):
        try:
            logo_file = pasta_dados_principia() / 'mr_logo_principia.png'
            if not logo_file.exists():
                logo_file.write_bytes(base64.b64decode(EMBEDDED_MR_LOGO_PNG_B64))
            return str(logo_file)
        except Exception:
            return ''

    def _get_logo(self):
        if self._embedded_logo is None:
            try:
                self._embedded_logo = tk.PhotoImage(data=EMBEDDED_MR_LOGO_PNG_B64)
            except Exception:
                self._embedded_logo = None
        return self._embedded_logo

    def _header(self, parent, title, subtitle):
        header = tk.Frame(parent, bg=self.COLORS['navy'], height=82)
        header.pack(fill='x')
        header.pack_propagate(False)

        logo = self._get_logo()
        if logo is not None:
            tk.Label(header, image=logo, bg=self.COLORS['navy']).pack(side='left', padx=(22, 14), pady=8)

        text_box = tk.Frame(header, bg=self.COLORS['navy'])
        text_box.pack(side='left', fill='y')
        ttk.Label(text_box, text=title, style='HeroTitle.TLabel').pack(anchor='w', pady=(15, 0))
        ttk.Label(text_box, text=subtitle, style='HeroSub.TLabel').pack(anchor='w', pady=(2, 0))

        tk.Label(
            header,
            text='MR | PRINCIPIA MINIMA',
            bg=self.COLORS['navy'],
            fg=self.COLORS['light_blue'],
            font=('Segoe UI', 9, 'bold'),
        ).pack(side='right', padx=24)
        return header

    def _white_card(self, parent, padding=(18, 14)):
        return ttk.Frame(parent, style='Card.TFrame', padding=padding)

    def _kpi_card(self, parent, title, value, subtitle=''):
        card = ttk.Frame(parent, style='Card.TFrame', padding=(16, 13))
        ttk.Label(card, text=title.upper(), style='CardTitle.TLabel').pack(anchor='w')
        ttk.Label(card, text=value, style='CardValue.TLabel').pack(anchor='w', pady=(5, 0))
        if subtitle:
            ttk.Label(card, text=subtitle, style='MutedWhite.TLabel', wraplength=190, justify='left').pack(anchor='w', pady=(3, 0))
        return card

    def _back_toolbar(self, parent, message=''):
        toolbar = ttk.Frame(parent, padding=(18, 11))
        toolbar.pack(fill='x')
        ttk.Button(toolbar, text='← Voltar', style='Secondary.TButton', command=self.mostrar_inicio).pack(side='left')
        if message:
            ttk.Label(toolbar, text=message, font=('Segoe UI', 9)).pack(side='right')
        return toolbar

    # -----------------------------------------------------------------
    # HOME
    # -----------------------------------------------------------------
    def mostrar_inicio(self):
        self.limpar()
        self.configure(bg=self.COLORS['background'])
        self._header(
            self,
            'PRINCIPIA MINIMA',
            'Otimização de corte de barras de cobre • Planejamento, histórico e reaproveitamento de retalhos',
        )

        body = ttk.Frame(self, padding=(20, 18))
        body.pack(fill='both', expand=True)

        intro = self._white_card(body, (20, 16))
        intro.pack(fill='x', pady=(0, 14))
        ttk.Label(intro, text='SELECIONE O MODO DE OPERAÇÃO', style='CardTitle.TLabel').pack(anchor='w')
        ttk.Label(
            intro,
            text='O motor matemático e os parâmetros do Principia Minima permanecem os mesmos; esta versão aprimora a operação visual no chão de fábrica.',
            style='White.TLabel',
            wraplength=1050,
            justify='left',
        ).pack(anchor='w', pady=(6, 0))

        cards = ttk.Frame(body)
        cards.pack(fill='both', expand=True)
        cards.columnconfigure(0, weight=1)
        cards.columnconfigure(1, weight=1)
        cards.columnconfigure(2, weight=1)
        cards.rowconfigure(0, weight=1)

        specs = [
            ('PLANEJAMENTO EMERGENCIAL', 'Estoque atual + demanda semanal. Usa barras novas e retalhos disponíveis e calcula o saldo final.', 'ABRIR EMERGENCIAL', self.mostrar_emergencial),
            ('PLANEJAMENTO INTELIGENTE', 'Demanda futura + Principia Lab. Considera barras, desperdício, fragmentação e valor futuro dos retalhos.', 'ABRIR PLANEJADO', self.mostrar_planejado),
            ('HISTÓRICO LOCAL', 'Consulta as otimizações registradas no SQLite local deste computador para rastreabilidade e estudos futuros.', 'ABRIR HISTÓRICO', self.mostrar_historico),
        ]

        for col, (title, text, button, command) in enumerate(specs):
            card = self._white_card(cards, (20, 18))
            card.grid(row=0, column=col, padx=(0 if col == 0 else 7, 0 if col == 2 else 7), sticky='nsew')
            ttk.Label(card, text=title, style='CardTitle.TLabel').pack(anchor='w')
            ttk.Label(card, text=text, style='White.TLabel', wraplength=320, justify='left').pack(anchor='w', pady=(10, 22))
            ttk.Button(card, text=button, style='Accent.TButton', command=command).pack(anchor='w')

        footer = tk.Label(
            self,
            text=f'Versão {VERSAO_INDUSTRIAL} • SQLite local • Interface corporativa • Dashboard final • Progresso com ETA',
            anchor='w',
            bg='#E6EBF0',
            fg=self.COLORS['text'],
            padx=16,
            pady=7,
            font=('Segoe UI', 9),
        )
        footer.pack(fill='x', side='bottom')

    # -----------------------------------------------------------------
    # PLANEJADO
    # -----------------------------------------------------------------
    def mostrar_planejado(self):
        self.limpar()
        self.caminho_demanda_planejado = None
        self._header(self, 'PLANEJAMENTO INTELIGENTE', 'Modelo CSPUL com referência histórica do Principia Lab')
        self._back_toolbar(self, 'Planejamento futuro')

        notebook = ttk.Notebook(self)
        notebook.pack(fill='both', expand=True, padx=18, pady=(0, 12))
        tab_setup = ttk.Frame(notebook, padding=14)
        tab_lab = ttk.Frame(notebook, padding=14)
        notebook.add(tab_setup, text='Configuração')
        notebook.add(tab_lab, text='Principia Lab')

        params = ttk.LabelFrame(tab_setup, text='Parâmetros físicos', padding=14, style='Card.TLabelframe')
        params.pack(fill='x', pady=(0, 12))
        fields = [
            ('Barra padrão (mm)', 'entry_barra_p', BARRA_PADRAO_DEFAULT),
            ('Kerf (mm)', 'entry_kerf_p', KERF_DEFAULT),
            ('Limite retalho (mm)', 'entry_retalho_p', LIMITE_RETALHO_DEFAULT),
            ('Desperdício máx. recomendado (mm)', 'entry_desperdicio_max_p', DESPERDICIO_MAX_RECOMENDADO_DEFAULT),
        ]
        for i, (label, attr, default) in enumerate(fields):
            ttk.Label(params, text=label, style='White.TLabel').grid(row=0, column=i, padx=8, sticky='w')
            entry = ttk.Entry(params, width=22)
            entry.insert(0, str(default))
            entry.grid(row=1, column=i, padx=8, pady=(5, 0), sticky='ew')
            params.columnconfigure(i, weight=1)
            setattr(self, attr, entry)

        file_card = ttk.LabelFrame(tab_setup, text='Demanda', padding=14, style='Card.TLabelframe')
        file_card.pack(fill='x', pady=(0, 12))
        ttk.Button(file_card, text='Selecionar demanda (.csv/.xlsx)', style='Accent.TButton', command=self.selecionar_demanda_planejado).pack(side='left')
        self.label_demanda_p = ttk.Label(file_card, text='Nenhum arquivo selecionado.', style='White.TLabel')
        self.label_demanda_p.pack(side='left', padx=14)

        run = ttk.Frame(tab_setup, style='Card.TFrame', padding=(18, 15))
        run.pack(fill='x')
        ttk.Label(run, text='EXECUÇÃO', style='CardTitle.TLabel').pack(anchor='w')
        ttk.Label(run, text='Ao iniciar, o sistema mostrará percentual, etapa atual e tempo restante estimado.', style='White.TLabel').pack(anchor='w', pady=(5, 10))
        ttk.Button(run, text='OTIMIZAR + GERAR PLANO VISUAL', style='Accent.TButton', command=self.processar_planejado).pack(anchor='w')

        lab_card = ttk.Frame(tab_lab, style='Card.TFrame', padding=(18, 16))
        lab_card.pack(fill='x')
        ttk.Label(lab_card, text='INTELIGÊNCIA HISTÓRICA', style='CardTitle.TLabel').pack(anchor='w')
        ttk.Button(lab_card, text='Selecionar Principia_Lab_resultados.xlsx', style='Accent.TButton', command=self.selecionar_lab_planejado).pack(anchor='w', pady=(10, 6))
        self.label_lab_p = ttk.Label(
            lab_card,
            text=(os.path.basename(self.caminho_lab_planejado) if self.caminho_lab_planejado else 'Sem Lab: será usado fallback por concentração'),
            style='White.TLabel',
        )
        self.label_lab_p.pack(anchor='w', pady=(2, 12))
        ttk.Label(lab_card, text='Horizonte de valor:', style='White.TLabel').pack(anchor='w')
        self.combo_horizonte_p = ttk.Combobox(lab_card, state='readonly', values=list(HORIZONTES_LAB.keys()), width=24)
        self.combo_horizonte_p.set('Média 15/30/60')
        self.combo_horizonte_p.pack(anchor='w', pady=(5, 0))

    # -----------------------------------------------------------------
    # EMERGENCIAL
    # -----------------------------------------------------------------
    def mostrar_emergencial(self):
        self.limpar()
        self.caminho_demanda_emergencial = None
        self.caminho_estoque_emergencial = None
        self._header(self, 'PLANEJAMENTO EMERGENCIAL', 'Demanda semanal + estoque atual, com acompanhamento visual do processamento')
        self._back_toolbar(self, 'Modo operacional')

        notebook = ttk.Notebook(self)
        notebook.pack(fill='both', expand=True, padx=18, pady=(0, 12))
        tab_input = ttk.Frame(notebook, padding=14)
        tab_stock = ttk.Frame(notebook, padding=14)
        notebook.add(tab_input, text='Demanda e parâmetros')
        notebook.add(tab_stock, text='Estoque atual')

        params = ttk.LabelFrame(tab_input, text='Parâmetros', padding=14, style='Card.TLabelframe')
        params.pack(fill='x', pady=(0, 12))
        fields = [
            ('Kerf (mm)', 'entry_kerf_e', KERF_DEFAULT),
            ('Limite retalho (mm)', 'entry_retalho_e', LIMITE_RETALHO_DEFAULT),
            ('Barra padrão (mm)', 'entry_barra_e', BARRA_PADRAO_DEFAULT),
            ('Desperdício máx. recomendado (mm)', 'entry_desperdicio_max_e', DESPERDICIO_MAX_RECOMENDADO_DEFAULT),
        ]
        for i, (label, attr, default) in enumerate(fields):
            ttk.Label(params, text=label, style='White.TLabel').grid(row=0, column=i, padx=8, sticky='w')
            entry = ttk.Entry(params, width=22)
            entry.insert(0, str(default))
            entry.grid(row=1, column=i, padx=8, pady=(5, 0), sticky='ew')
            params.columnconfigure(i, weight=1)
            setattr(self, attr, entry)

        demand = ttk.LabelFrame(tab_input, text='Demanda semanal', padding=14, style='Card.TLabelframe')
        demand.pack(fill='x', pady=(0, 12))
        ttk.Button(demand, text='Selecionar demanda (.csv/.xlsx)', style='Accent.TButton', command=self.selecionar_demanda_emergencial).pack(side='left')
        self.label_demanda_e = ttk.Label(demand, text='Nenhum arquivo selecionado.', style='White.TLabel')
        self.label_demanda_e.pack(side='left', padx=14)

        run = ttk.Frame(tab_input, style='Card.TFrame', padding=(18, 15))
        run.pack(fill='x')
        ttk.Label(run, text='EXECUÇÃO', style='CardTitle.TLabel').pack(anchor='w')
        ttk.Label(run, text='A barra de progresso considera leitura, otimização, simulação do estoque e exportação.', style='White.TLabel').pack(anchor='w', pady=(5, 10))
        ttk.Button(run, text='OTIMIZAR SEMANA E GERAR EXCEL', style='Accent.TButton', command=self.processar_emergencial).pack(anchor='w')

        stock_file = ttk.LabelFrame(tab_stock, text='Planilha de estoque', padding=14, style='Card.TLabelframe')
        stock_file.pack(fill='x', pady=(0, 12))
        ttk.Button(stock_file, text='Selecionar estoque (.csv/.xlsx)', style='Accent.TButton', command=self.selecionar_estoque_emergencial).pack(side='left')
        self.label_estoque_e = ttk.Label(stock_file, text='Nenhum arquivo de estoque selecionado.', style='White.TLabel')
        self.label_estoque_e.pack(side='left', padx=14)

        manual = ttk.LabelFrame(tab_stock, text='Inserção manual', padding=14, style='Card.TLabelframe')
        manual.pack(fill='x', pady=(0, 12))
        ttk.Label(manual, text='Diâmetro', style='White.TLabel').grid(row=0, column=0, padx=5, sticky='w')
        self.entry_diametro_estoque_e = ttk.Entry(manual, width=14)
        self.entry_diametro_estoque_e.grid(row=1, column=0, padx=5, pady=(4, 0))
        ttk.Label(manual, text='Comprimento (mm)', style='White.TLabel').grid(row=0, column=1, padx=5, sticky='w')
        self.entry_comprimento_estoque_e = ttk.Entry(manual, width=18)
        self.entry_comprimento_estoque_e.grid(row=1, column=1, padx=5, pady=(4, 0))
        ttk.Label(manual, text='Quantidade', style='White.TLabel').grid(row=0, column=2, padx=5, sticky='w')
        self.entry_quantidade_estoque_e = ttk.Entry(manual, width=14)
        self.entry_quantidade_estoque_e.grid(row=1, column=2, padx=5, pady=(4, 0))
        ttk.Button(manual, text='Adicionar', style='Accent.TButton', command=self.adicionar_estoque_emergencial).grid(row=1, column=3, padx=8)
        ttk.Button(manual, text='Remover selecionado', style='Secondary.TButton', command=self.remover_estoque_emergencial).grid(row=1, column=4, padx=5)

        table_frame = ttk.Frame(tab_stock)
        table_frame.pack(fill='both', expand=True)
        self.tabela_estoque_e = ttk.Treeview(table_frame, columns=('diametro', 'comprimento', 'quantidade'), show='headings', height=9)
        self.tabela_estoque_e.heading('diametro', text='DIÂMETRO')
        self.tabela_estoque_e.heading('comprimento', text='COMPRIMENTO (mm)')
        self.tabela_estoque_e.heading('quantidade', text='QUANTIDADE')
        self.tabela_estoque_e.column('diametro', anchor='center', width=150)
        self.tabela_estoque_e.column('comprimento', anchor='center', width=220)
        self.tabela_estoque_e.column('quantidade', anchor='center', width=150)
        self.tabela_estoque_e.pack(fill='both', expand=True)

    def mostrar_historico(self):
        df = ler_historico_execucoes(300)
        win = tk.Toplevel(self)
        win.title('Principia Minima - Histórico de otimizações')
        win.geometry('1220x650')
        win.minsize(980, 560)
        win.configure(bg=self.COLORS['background'])
        self._header(win, 'HISTÓRICO DE OTIMIZAÇÕES', 'Registros armazenados no SQLite local deste computador')

        content = ttk.Frame(win, padding=(18, 14))
        content.pack(fill='both', expand=True)
        card = ttk.Frame(content, style='Card.TFrame', padding=(14, 12))
        card.pack(fill='both', expand=True)

        cols = ('data_hora', 'modo', 'horizonte_lab', 'arquivo_demanda', 'excel_saida')
        labels = {
            'data_hora': 'DATA / HORA',
            'modo': 'MODO',
            'horizonte_lab': 'HORIZONTE',
            'arquivo_demanda': 'ARQUIVO DE DEMANDA',
            'excel_saida': 'ARQUIVO DE SAÍDA',
        }
        tree = ttk.Treeview(card, columns=cols, show='headings')
        for c in cols:
            tree.heading(c, text=labels[c])
            tree.column(c, width=170 if c not in {'arquivo_demanda', 'excel_saida'} else 350, anchor='center' if c in {'data_hora','modo','horizonte_lab'} else 'w')
        for _, row in df.iterrows():
            tree.insert('', 'end', values=[row.get(c, '') for c in cols])
        vbar = ttk.Scrollbar(card, orient='vertical', command=tree.yview)
        hbar = ttk.Scrollbar(card, orient='horizontal', command=tree.xview)
        tree.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set)
        tree.grid(row=0, column=0, sticky='nsew')
        vbar.grid(row=0, column=1, sticky='ns')
        hbar.grid(row=1, column=0, sticky='ew')
        card.rowconfigure(0, weight=1)
        card.columnconfigure(0, weight=1)

        footer = tk.Label(win, text=f'Banco local: {caminho_banco_principia()}', anchor='w', bg='#E6EBF0', fg=self.COLORS['text'], padx=14, pady=6, font=('Segoe UI', 9))
        footer.pack(fill='x', side='bottom')

    # -----------------------------------------------------------------
    # PROGRESSO / THREAD
    # -----------------------------------------------------------------
    def _run_with_progress(self, title, worker, on_success):
        q = queue.Queue()
        dlg = ProgressoSolverDialog(self, title, self.COLORS)

        def emit(kind, *args):
            q.put((kind, args))

        def runner():
            try:
                payload = worker(emit)
                q.put(('result', (payload,)))
            except Exception as exc:
                q.put(('error', (str(exc),)))

        threading.Thread(target=runner, daemon=True).start()

        def poll():
            try:
                while True:
                    kind, args = q.get_nowait()
                    if kind == 'stage':
                        dlg.set_stage(*args)
                    elif kind == 'exact':
                        dlg.set_exact(*args)
                    elif kind == 'result':
                        dlg.finish()
                        payload = args[0]
                        dlg.grab_release()
                        dlg.after(220, dlg.destroy)
                        on_success(payload)
                        return
                    elif kind == 'error':
                        dlg.grab_release()
                        dlg.destroy()
                        messagebox.showerror('Erro de Processamento', args[0])
                        return
            except queue.Empty:
                pass
            self.after(120, poll)

        poll()

    # -----------------------------------------------------------------
    # PROCESSAMENTO PLANEJADO COM PROGRESSO REAL POR DIÂMETRO
    # -----------------------------------------------------------------
    def processar_planejado(self):
        if not self.caminho_demanda_planejado:
            messagebox.showwarning('Demanda', 'Selecione a planilha de demanda.')
            return
        try:
            params = {
                'tamanho_barra': float(self.entry_barra_p.get().replace(',', '.')),
                'kerf': float(self.entry_kerf_p.get().replace(',', '.')),
                'limite': float(self.entry_retalho_p.get().replace(',', '.')),
                'desperdicio_max': float(self.entry_desperdicio_max_p.get().replace(',', '.')),
                'horizonte_nome': self.combo_horizonte_p.get(),
            }
            if params['tamanho_barra'] <= 0 or params['kerf'] < 0 or params['limite'] < 0 or params['desperdicio_max'] < 0:
                raise ValueError('Parâmetros físicos inválidos.')
            demanda_path = self.caminho_demanda_planejado
            lab_path = self.caminho_lab_planejado
        except Exception as exc:
            messagebox.showerror('Parâmetros', str(exc))
            return

        def worker(emit):
            emit('stage', 2, 12, 'Lendo e validando a demanda...', 4)
            df_detalhada = ler_demanda_csv(demanda_path)
            df_solver = agrupar_demanda_para_solver(df_detalhada)
            horizont = HORIZONTES_LAB.get(params['horizonte_nome'], 'MEDIA')

            emit('stage', 12, 20, 'Carregando o modelo histórico do Principia Lab...', 3)
            modelo = None
            if lab_path and os.path.exists(lab_path):
                modelo = ModeloValorRetalho(lab_path, horizont)

            diametros = sorted(df_solver['DIAMETRO'].unique())
            total_d = max(len(diametros), 1)
            planos, resumos, comparacoes = [], [], []

            for i, diam in enumerate(diametros, start=1):
                start_p = 20 + (i - 1) * 58 / total_d
                end_p = 20 + i * 58 / total_d
                remaining_solver = (total_d - i + 1) * (TEMPO_LIMITE_OTIMIZACAO_MS / 1000.0)
                emit('stage', start_p, end_p, f'Otimizando Ø{diam:g} • diâmetro {i} de {total_d}...', remaining_solver)
                grupo = df_solver[df_solver['DIAMETRO'] == diam].copy()
                linhas, resumo, comp = otimizar_planejado_por_diametro(
                    diam,
                    grupo,
                    params['tamanho_barra'],
                    params['kerf'],
                    params['limite'],
                    params['desperdicio_max'],
                    modelo_valor=modelo,
                )
                planos.extend(linhas)
                resumos.append(resumo)
                comparacoes.extend(comp)
                emit('exact', end_p, f'Ø{diam:g} concluído.', max((total_d-i) * 60 + 10, 0))

            plano = pd.DataFrame(planos)
            resumo = pd.DataFrame(resumos)
            comparacao = pd.DataFrame(comparacoes)

            emit('stage', 78, 86, 'Aplicando rastreabilidade e valor dos retalhos...', 5)
            plano = adicionar_rastreabilidade_ao_plano(plano, df_detalhada)
            plano = anotar_valor_retalhos(plano, modelo, params['limite'], horizont)

            emit('stage', 86, 94, 'Gerando Excel operacional...', 4)
            excel = exportar_excel_planejado(
                demanda_path,
                plano,
                resumo,
                df_detalhada.drop(columns=['_ORDEM'], errors='ignore'),
                comparacao=comparacao,
                arquivo_lab=lab_path,
            )

            emit('stage', 94, 99, 'Gerando plano visual para impressão...', 3)
            visual = gerar_folha_visual_html(plano, excel, logo_path=self.logo_path, titulo='Principia Minima - Planejamento de Corte')

            return {
                'modo': 'PLANEJADO', 'plano': plano, 'resumo': resumo,
                'comparacao': comparacao, 'excel': excel, 'visual': visual,
                'faltas': pd.DataFrame(), 'estoque_final': pd.DataFrame(),
                'limite': params['limite'], 'horizonte': horizont,
                'parametros': {
                    'barra_padrao': params['tamanho_barra'], 'kerf': params['kerf'],
                    'limite_retalho': params['limite'], 'desperdicio_max': params['desperdicio_max'],
                },
            }

        def success(data):
            self._ultimo_plano = data['plano']
            self._ultima_comparacao = data['comparacao']
            self._ultimo_html = data['visual']
            self._ultimo_estoque_final = data['estoque_final']
            self._ultimo_limite_retalho = data['limite']
            self._ultima_execucao_id = registrar_execucao_historico(
                modo='PLANEJADO', arquivo_demanda=demanda_path, resumo=data['resumo'],
                plano=data['plano'], excel_saida=data['excel'], folha_visual=data['visual'],
                arquivo_lab=lab_path, horizonte_lab=data['horizonte'], parametros=data['parametros'],
            )
            self.mostrar_resultado('PLANEJADO', data['resumo'], data['excel'], data['faltas'])

        self._run_with_progress('Principia Minima • Planejado', worker, success)

    # -----------------------------------------------------------------
    # PROCESSAMENTO EMERGENCIAL COM PROGRESSO REAL POR DIÂMETRO
    # -----------------------------------------------------------------
    def processar_emergencial(self):
        if not self.caminho_demanda_emergencial:
            messagebox.showwarning('Demanda', 'Selecione a planilha de demanda semanal.')
            return
        try:
            params = {
                'kerf': float(self.entry_kerf_e.get().replace(',', '.')),
                'limite': float(self.entry_retalho_e.get().replace(',', '.')),
                'barra_padrao': float(self.entry_barra_e.get().replace(',', '.')),
                'desperdicio_max': float(self.entry_desperdicio_max_e.get().replace(',', '.')),
            }
            if params['kerf'] < 0 or params['limite'] < 0 or params['barra_padrao'] <= 0 or params['desperdicio_max'] < 0:
                raise ValueError('Parâmetros físicos inválidos.')
            demanda_path = self.caminho_demanda_emergencial
            estoque_path = self.caminho_estoque_emergencial
            # Captura widgets de estoque no thread principal (Tkinter não é thread-safe).
            estoque = self.obter_estoque_emergencial(params['barra_padrao'])
            lab_path = self.caminho_lab_planejado
        except Exception as exc:
            messagebox.showerror('Parâmetros / Estoque', str(exc))
            return

        def worker(emit):
            emit('stage', 2, 12, 'Lendo e validando a demanda semanal...', 4)
            df_detalhada = ler_demanda_csv(demanda_path)
            df_solver = agrupar_demanda_para_solver(df_detalhada)

            diametros = sorted(df_solver['DIAMETRO'].unique())
            total_d = max(len(diametros), 1)
            planos, resumos, faltas_total, recomendacoes_total = [], [], [], []

            for i, diam in enumerate(diametros, start=1):
                start_p = 14 + (i - 1) * 58 / total_d
                end_p = 14 + i * 58 / total_d
                emit('stage', start_p, end_p, f'Otimizando estoque Ø{diam:g} • diâmetro {i} de {total_d}...', (total_d-i+1) * 60)
                demanda_d = df_solver[df_solver['DIAMETRO'] == diam].copy()
                estoque_d = estoque[estoque['DIAMETRO'] == diam].copy()
                linhas, resumo, faltas, recs = otimizar_emergencial_por_diametro(
                    diam, demanda_d, estoque_d, params['kerf'], params['limite'],
                    params['desperdicio_max'], params['barra_padrao'],
                )
                planos.extend(linhas); resumos.append(resumo); faltas_total.extend(faltas); recomendacoes_total.extend(recs)
                emit('exact', end_p, f'Ø{diam:g} concluído.', max((total_d-i) * 60 + 15, 0))

            plano = pd.DataFrame(planos)
            resumo = pd.DataFrame(resumos)
            faltas = pd.DataFrame(faltas_total)
            recomendacoes = pd.DataFrame(recomendacoes_total)

            emit('stage', 72, 80, 'Aplicando rastreabilidade do plano...', 5)
            plano = adicionar_rastreabilidade_ao_plano(plano, df_detalhada)

            emit('stage', 80, 86, 'Avaliando valor futuro dos retalhos...', 4)
            modelo = None
            if lab_path and os.path.exists(lab_path):
                try:
                    modelo = ModeloValorRetalho(lab_path, 'MEDIA')
                except Exception:
                    modelo = None
            plano = anotar_valor_retalhos(plano, modelo, params['limite'], 'MEDIA')

            emit('stage', 86, 92, 'Simulando estoque final e movimentações...', 4)
            estoque_final, movimentos = simular_estoque_final(estoque, plano, params['limite'])

            emit('stage', 92, 97, 'Gerando Excel operacional...', 4)
            excel = exportar_excel_emergencial(
                demanda_path, plano, resumo, faltas, recomendacoes,
                df_detalhada.drop(columns=['_ORDEM'], errors='ignore'), estoque,
                estoque_final=estoque_final, movimentos=movimentos,
            )

            emit('stage', 97, 99, 'Gerando plano visual para impressão...', 2)
            visual = gerar_folha_visual_html(plano, excel, logo_path=self.logo_path, titulo='Principia Minima - Corte Emergencial')

            return {
                'modo': 'EMERGENCIAL', 'plano': plano, 'resumo': resumo,
                'comparacao': pd.DataFrame(), 'excel': excel, 'visual': visual,
                'faltas': faltas, 'estoque_final': estoque_final, 'limite': params['limite'],
                'parametros': {
                    'barra_padrao': params['barra_padrao'], 'kerf': params['kerf'],
                    'limite_retalho': params['limite'], 'desperdicio_max': params['desperdicio_max'],
                },
            }

        def success(data):
            self._ultimo_plano = data['plano']
            self._ultima_comparacao = data['comparacao']
            self._ultimo_html = data['visual']
            self._ultimo_estoque_final = data['estoque_final']
            self._ultimo_limite_retalho = data['limite']
            self._ultima_execucao_id = registrar_execucao_historico(
                modo='EMERGENCIAL', arquivo_demanda=demanda_path, arquivo_estoque=estoque_path,
                resumo=data['resumo'], plano=data['plano'], excel_saida=data['excel'],
                folha_visual=data['visual'], arquivo_lab=lab_path, horizonte_lab='MEDIA',
                parametros=data['parametros'], estoque_inicial=estoque, estoque_final=data['estoque_final'],
            )
            self.mostrar_resultado('EMERGENCIAL', data['resumo'], data['excel'], data['faltas'])

        self._run_with_progress('Principia Minima • Emergencial', worker, success)

    # -----------------------------------------------------------------
    # DASHBOARD FINAL
    # -----------------------------------------------------------------
    def _fmt(self, value, decimals=1):
        try:
            return f'{float(value):,.{decimals}f}'.replace(',', 'X').replace('.', ',').replace('X', '.')
        except Exception:
            return str(value)

    def mostrar_resultado(self, modo, resumo, caminho_excel, faltas):
        win = tk.Toplevel(self)
        win.title(f'Principia Minima - Dashboard final - {modo}')
        win.geometry('1360x790')
        win.minsize(1120, 680)
        win.configure(bg=self.COLORS['background'])
        self._header(win, f'DASHBOARD FINAL • {modo}', 'Resumo da otimização concluída e acesso aos documentos operacionais')

        notebook = ttk.Notebook(win)
        notebook.pack(fill='both', expand=True, padx=18, pady=(14, 10))
        dash = ttk.Frame(notebook, padding=12)
        detail = ttk.Frame(notebook, padding=12)
        notebook.add(dash, text='Dashboard')
        notebook.add(detail, text='Detalhamento')
        if modo == 'PLANEJADO' and isinstance(self._ultima_comparacao, pd.DataFrame) and not self._ultima_comparacao.empty:
            comp_tab = ttk.Frame(notebook, padding=12)
            notebook.add(comp_tab, text='Comparação de retalhos')
            self._build_comparison_tab(comp_tab)
        if modo == 'EMERGENCIAL' and isinstance(self._ultimo_estoque_final, pd.DataFrame) and not self._ultimo_estoque_final.empty:
            stock_tab = ttk.Frame(notebook, padding=12)
            notebook.add(stock_tab, text='Estoque final')
            self._build_stock_tab(stock_tab)

        total_fontes = int(resumo['TOTAL_FONTES_USADAS'].sum()) if 'TOTAL_FONTES_USADAS' in resumo.columns else int(resumo.get('BARRAS_NOVAS_USADAS', pd.Series(dtype=float)).sum())
        total_desp = float(resumo['DESPERDICIO_REAL_MM'].sum()) if 'DESPERDICIO_REAL_MM' in resumo.columns else 0.0
        total_ret = float(resumo['RETALHO_REAPROVEITAVEL_MM'].sum()) if 'RETALHO_REAPROVEITAVEL_MM' in resumo.columns else 0.0
        aproveitamento = float(resumo['APROVEITAMENTO_PERCENTUAL'].mean()) if 'APROVEITAMENTO_PERCENTUAL' in resumo.columns and not resumo.empty else 0.0
        faltantes = int(resumo['PECAS_FALTANTES'].sum()) if 'PECAS_FALTANTES' in resumo.columns else 0
        diametros = int(resumo['DIAMETRO'].nunique()) if 'DIAMETRO' in resumo.columns else len(resumo)

        cards = ttk.Frame(dash)
        cards.pack(fill='x')
        values = [
            ('Diâmetros', str(diametros), 'grupos processados'),
            ('Fontes usadas', str(total_fontes), 'barras/retalhos'),
            ('Desperdício total', f'{self._fmt(total_desp)} mm', 'soma consolidada'),
            ('Retalho útil', f'{self._fmt(total_ret)} mm', 'reaproveitável'),
            ('Aproveitamento médio', f'{self._fmt(aproveitamento, 2)}%', 'média por diâmetro'),
            ('Peças faltantes', str(faltantes), '0 = atendimento completo'),
        ]
        for i, item in enumerate(values):
            cards.columnconfigure(i, weight=1)
            self._kpi_card(cards, *item).grid(row=0, column=i, padx=(0 if i == 0 else 5, 0 if i == len(values)-1 else 5), sticky='nsew')

        progress_card = ttk.Frame(dash, style='Card.TFrame', padding=(18, 15))
        progress_card.pack(fill='x', pady=14)
        ttk.Label(progress_card, text='PROCESSAMENTO CONCLUÍDO', style='CardTitle.TLabel').pack(anchor='w')
        done = ttk.Progressbar(progress_card, maximum=100, value=100, style='Overall.Horizontal.TProgressbar')
        done.pack(fill='x', pady=(10, 4))
        ttk.Label(progress_card, text='100% • Plano final disponível para análise e impressão', style='MutedWhite.TLabel').pack(anchor='w')

        actions = ttk.Frame(dash)
        actions.pack(fill='x')
        ttk.Button(actions, text='Abrir Excel', style='Accent.TButton', command=lambda: self.abrir_arquivo(caminho_excel)).pack(side='left', padx=(0, 8))
        ttk.Button(actions, text='Plano visual', style='Accent.TButton', command=lambda: mostrar_animacao_corte(self, self._ultimo_plano, self._ultimo_limite_retalho)).pack(side='left', padx=8)
        if self._ultimo_html:
            ttk.Button(actions, text='Folha para imprimir', style='Accent.TButton', command=lambda: webbrowser.open(Path(self._ultimo_html).resolve().as_uri())).pack(side='left', padx=8)
        ttk.Button(actions, text='Abrir pasta', style='Secondary.TButton', command=lambda: self.abrir_pasta(os.path.dirname(caminho_excel))).pack(side='left', padx=8)
        ttk.Button(actions, text='Fechar', style='Secondary.TButton', command=win.destroy).pack(side='right')

        self._build_summary_table(detail, resumo)

    def _build_summary_table(self, parent, resumo):
        frame = ttk.Frame(parent)
        frame.pack(fill='both', expand=True)
        preferred = [
            'DIAMETRO', 'DEMANDA_TOTAL_PECAS', 'PECAS_ATENDIDAS', 'PECAS_FALTANTES',
            'BARRAS_NOVAS_USADAS', 'RETALHOS_USADOS', 'TOTAL_FONTES_USADAS',
            'DESPERDICIO_REAL_MM', 'RETALHO_REAPROVEITAVEL_MM',
            'APROVEITAMENTO_PERCENTUAL', 'STATUS',
        ]
        cols = [c for c in preferred if c in resumo.columns]
        tree = ttk.Treeview(frame, columns=cols, show='headings')
        for c in cols:
            tree.heading(c, text=c.replace('_', ' '))
            tree.column(c, anchor='center', width=155 if c != 'STATUS' else 380)
        for _, row in resumo.iterrows():
            vals = []
            for c in cols:
                v = row.get(c, '')
                vals.append(f'{v:.2f}' if isinstance(v, float) else v)
            tree.insert('', 'end', values=vals)
        vbar = ttk.Scrollbar(frame, orient='vertical', command=tree.yview)
        hbar = ttk.Scrollbar(frame, orient='horizontal', command=tree.xview)
        tree.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set)
        tree.grid(row=0, column=0, sticky='nsew')
        vbar.grid(row=0, column=1, sticky='ns')
        hbar.grid(row=1, column=0, sticky='ew')
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)

    def _build_comparison_tab(self, parent):
        df = self._ultima_comparacao.copy()
        cols = list(df.columns)
        tree = ttk.Treeview(parent, columns=cols, show='headings')
        for c in cols:
            tree.heading(c, text=c.replace('_', ' '))
            tree.column(c, width=145, anchor='center')
        for _, row in df.iterrows():
            tree.insert('', 'end', values=[row.get(c, '') for c in cols])
        tree.pack(fill='both', expand=True)

    def _build_stock_tab(self, parent):
        df = self._ultimo_estoque_final.copy()
        cols = list(df.columns)
        tree = ttk.Treeview(parent, columns=cols, show='headings')
        for c in cols:
            tree.heading(c, text=c.replace('_', ' '))
            tree.column(c, width=150, anchor='center')
        for _, row in df.iterrows():
            tree.insert('', 'end', values=[row.get(c, '') for c in cols])
        tree.pack(fill='both', expand=True)





# =====================================================================
# FACTORY INTELLIGENCE V3.2
# Confirmação do operador + base de modelos realmente utilizados
# + interface dark moderna para chão de fábrica
# =====================================================================

def inicializar_feedback_operador():
    """Cria as tabelas de validação operacional sem alterar o histórico existente."""
    inicializar_banco()
    with sqlite3.connect(caminho_banco_principia()) as con:
        con.execute(
            """
            CREATE TABLE IF NOT EXISTS feedback_operador (
                id_feedback INTEGER PRIMARY KEY AUTOINCREMENT,
                id_execucao TEXT NOT NULL UNIQUE,
                usado_modelo INTEGER NOT NULL,
                data_hora TEXT NOT NULL,
                FOREIGN KEY(id_execucao) REFERENCES execucoes(id_execucao)
            )
            """
        )
        con.execute(
            """
            CREATE TABLE IF NOT EXISTS modelos_usados (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                id_execucao TEXT NOT NULL,
                data_confirmacao TEXT NOT NULL,
                modo TEXT,
                id_barra TEXT,
                id_padrao TEXT,
                diametro REAL,
                tipo_fonte TEXT,
                comprimento_fonte_mm REAL,
                esquema_corte TEXT,
                sobra_mm REAL,
                classificacao_sobra TEXT,
                valor_v15 REAL,
                valor_v30 REAL,
                valor_v60 REAL,
                valor_futuro REAL,
                piv_linhas_atendidas TEXT,
                FOREIGN KEY(id_execucao) REFERENCES execucoes(id_execucao)
            )
            """
        )
        con.execute(
            "CREATE INDEX IF NOT EXISTS idx_modelos_usados_execucao ON modelos_usados(id_execucao)"
        )
        con.execute(
            "CREATE INDEX IF NOT EXISTS idx_modelos_usados_diametro ON modelos_usados(diametro)"
        )
        con.commit()


def registrar_feedback_operador(id_execucao, usado_modelo, plano=None):
    """
    Registra a decisão do operador.

    Somente quando usado_modelo=True as linhas físicas do plano são copiadas
    para MODELOS_USADOS. Assim, estudos futuros podem distinguir claramente
    'plano proposto pelo algoritmo' de 'plano realmente executado na fábrica'.
    """
    if not id_execucao:
        raise ValueError("Não foi possível identificar a execução atual.")

    inicializar_feedback_operador()
    agora = datetime.now().isoformat(timespec="seconds")
    usado_int = 1 if bool(usado_modelo) else 0

    with sqlite3.connect(caminho_banco_principia()) as con:
        con.execute(
            """
            INSERT INTO feedback_operador (
                id_execucao, usado_modelo, data_hora
            ) VALUES (?, ?, ?)
            ON CONFLICT(id_execucao) DO UPDATE SET
                usado_modelo=excluded.usado_modelo,
                data_hora=excluded.data_hora
            """,
            (id_execucao, usado_int, agora),
        )

        # Se o operador corrigir a resposta, reconstruímos a fotografia validada.
        con.execute(
            "DELETE FROM modelos_usados WHERE id_execucao = ?",
            (id_execucao,),
        )

        if usado_int and isinstance(plano, pd.DataFrame) and not plano.empty:
            for _, row in plano.iterrows():
                con.execute(
                    """
                    INSERT INTO modelos_usados (
                        id_execucao, data_confirmacao, modo,
                        id_barra, id_padrao, diametro, tipo_fonte,
                        comprimento_fonte_mm, esquema_corte, sobra_mm,
                        classificacao_sobra, valor_v15, valor_v30,
                        valor_v60, valor_futuro, piv_linhas_atendidas
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        id_execucao,
                        agora,
                        str(row.get("MODO", "")),
                        str(row.get("ID_BARRA", "")),
                        str(row.get("ID_PADRAO", "")),
                        _float_or_none(row.get("DIAMETRO")),
                        str(row.get("TIPO_FONTE", "")),
                        _float_or_none(row.get("COMPRIMENTO_FONTE_MM")),
                        str(row.get("ESQUEMA_DE_CORTE", "")),
                        _float_or_none(row.get("SOBRA_POR_BARRA_MM")),
                        str(row.get("CLASSIFICACAO_SOBRA", "")),
                        _float_or_none(row.get("VALOR_V15_MM")),
                        _float_or_none(row.get("VALOR_V30_MM")),
                        _float_or_none(row.get("VALOR_V60_MM")),
                        _float_or_none(row.get("VALOR_FUTURO_CRITERIO_MM")),
                        str(
                            row.get(
                                "PIV_OFERTA_LINHAS_ATENDIDAS",
                                row.get("PIV_LINHAS_ATENDIDAS", ""),
                            )
                        ),
                    ),
                )
        con.commit()

    return "USADO" if usado_int else "NÃO USADO"


def ler_historico_execucoes_feedback(limite=300):
    inicializar_feedback_operador()
    with sqlite3.connect(caminho_banco_principia()) as con:
        return pd.read_sql_query(
            """
            SELECT
                e.id_execucao,
                e.data_hora,
                e.modo,
                e.horizonte_lab,
                CASE
                    WHEN f.usado_modelo = 1 THEN 'USADO'
                    WHEN f.usado_modelo = 0 THEN 'NÃO USADO'
                    ELSE 'AGUARDANDO'
                END AS confirmacao_operador,
                e.arquivo_demanda,
                e.excel_saida
            FROM execucoes e
            LEFT JOIN feedback_operador f
                ON f.id_execucao = e.id_execucao
            ORDER BY e.data_hora DESC
            LIMIT ?
            """,
            con,
            params=(int(limite),),
        )


class PrincipiaMinimaFactoryApp(PrincipiaMinimaModernApp):
    """Interface V3.2: moderna, escura e orientada à operação da fábrica."""

    COLORS = {
        'navy': '#07131F',
        'blue': '#0B6FA4',
        'light_blue': '#7DD3FC',
        'green': '#22C55E',
        'green_light': '#123A2A',
        'amber': '#F59E0B',
        'amber_light': '#3A2B10',
        'gray': '#64748B',
        'gray_light': '#1A2635',
        'white': '#FFFFFF',
        'background': '#08111D',
        'surface': '#0F1C2B',
        'surface_2': '#142437',
        'text': '#E7EEF7',
        'muted': '#91A4B8',
        'border': '#263A4F',
        'danger': '#EF4444',
        'cyan': '#22D3EE',
    }

    def __init__(self):
        self._ultima_execucao_id = None
        inicializar_feedback_operador()
        super().__init__()
        self.title('Principia Minima • Factory Intelligence')
        self.configure(bg=self.COLORS['background'])

    # -------------------------------------------------------------
    # TEMA MODERNO / DARK
    # -------------------------------------------------------------
    def _configurar_estilo(self):
        style = ttk.Style(self)
        if 'clam' in style.theme_names():
            style.theme_use('clam')

        c = self.COLORS
        self.option_add('*tearOff', False)

        style.configure('TFrame', background=c['background'])
        style.configure('TLabel', background=c['background'], foreground=c['text'])
        style.configure('White.TLabel', background=c['surface'], foreground=c['text'])
        style.configure('MutedWhite.TLabel', background=c['surface'], foreground=c['muted'], font=('Segoe UI', 9))
        style.configure('Section.TLabel', background=c['background'], foreground=c['light_blue'], font=('Segoe UI', 12, 'bold'))
        style.configure('Titulo.TLabel', background=c['background'], foreground=c['white'], font=('Segoe UI', 20, 'bold'))
        style.configure('Subtitulo.TLabel', background=c['background'], foreground=c['muted'], font=('Segoe UI', 10))
        style.configure('HeroTitle.TLabel', background=c['navy'], foreground=c['white'], font=('Segoe UI Semibold', 20))
        style.configure('HeroSub.TLabel', background=c['navy'], foreground=c['light_blue'], font=('Segoe UI', 10))
        style.configure('Card.TFrame', background=c['surface'], relief='solid', borderwidth=1)
        style.configure('CardTitle.TLabel', background=c['surface'], foreground=c['muted'], font=('Segoe UI', 9, 'bold'))
        style.configure('CardValue.TLabel', background=c['surface'], foreground=c['white'], font=('Segoe UI Semibold', 22))
        style.configure('Card.TLabelframe', background=c['surface'], borderwidth=1, relief='solid')
        style.configure('Card.TLabelframe.Label', background=c['surface'], foreground=c['light_blue'], font=('Segoe UI', 10, 'bold'))

        style.configure('TNotebook', background=c['background'], borderwidth=0)
        style.configure('TNotebook.Tab', background=c['surface_2'], foreground=c['muted'], padding=(18, 10), font=('Segoe UI', 10, 'bold'))
        style.map(
            'TNotebook.Tab',
            background=[('selected', c['surface']), ('active', '#1A314A')],
            foreground=[('selected', c['white']), ('active', c['white'])],
        )

        style.configure(
            'Treeview',
            rowheight=31,
            font=('Segoe UI', 9),
            background=c['surface'],
            fieldbackground=c['surface'],
            foreground=c['text'],
            bordercolor=c['border'],
        )
        style.configure(
            'Treeview.Heading',
            background=c['surface_2'],
            foreground=c['light_blue'],
            font=('Segoe UI', 9, 'bold'),
            padding=(6, 8),
            relief='flat',
        )
        style.map('Treeview', background=[('selected', '#16496A')], foreground=[('selected', c['white'])])
        style.map('Treeview.Heading', background=[('active', '#1A314A')])

        style.configure('TEntry', fieldbackground='#0B1724', foreground=c['text'], insertcolor=c['white'], bordercolor=c['border'], padding=7)
        style.configure('TCombobox', fieldbackground='#0B1724', foreground=c['text'], background=c['surface_2'], arrowcolor=c['light_blue'], padding=5)
        style.map('TCombobox', fieldbackground=[('readonly', '#0B1724')], foreground=[('readonly', c['text'])])

        style.configure('Accent.TButton', font=('Segoe UI', 9, 'bold'), padding=(14, 9), background=c['blue'], foreground=c['white'], borderwidth=0)
        style.map('Accent.TButton', background=[('active', '#0D83BF'), ('pressed', '#09577E')])
        style.configure('Secondary.TButton', font=('Segoe UI', 9, 'bold'), padding=(12, 8), background=c['surface_2'], foreground=c['text'], borderwidth=0)
        style.map('Secondary.TButton', background=[('active', '#1A314A'), ('pressed', '#0B1724')])
        style.configure('Success.TButton', font=('Segoe UI', 9, 'bold'), padding=(14, 10), background=c['green'], foreground='#07130C', borderwidth=0)
        style.map('Success.TButton', background=[('active', '#34D399')])
        style.configure('Danger.TButton', font=('Segoe UI', 9, 'bold'), padding=(14, 10), background=c['danger'], foreground=c['white'], borderwidth=0)
        style.map('Danger.TButton', background=[('active', '#F87171')])
        style.configure('Acao.TButton', font=('Segoe UI', 10, 'bold'), padding=(14, 10), background=c['blue'], foreground=c['white'], borderwidth=0)
        style.map('Acao.TButton', background=[('active', '#0D83BF'), ('pressed', '#09577E')])
        style.configure('Overall.Horizontal.TProgressbar', troughcolor='#132235', background=c['cyan'], thickness=18, borderwidth=0)

    def _header(self, parent, title, subtitle):
        header = tk.Frame(parent, bg=self.COLORS['navy'], height=92)
        header.pack(fill='x')
        header.pack_propagate(False)

        accent = tk.Frame(header, bg=self.COLORS['cyan'], width=5)
        accent.pack(side='left', fill='y')

        logo = self._get_logo()
        if logo is not None:
            tk.Label(header, image=logo, bg=self.COLORS['navy']).pack(side='left', padx=(22, 16), pady=10)

        text_box = tk.Frame(header, bg=self.COLORS['navy'])
        text_box.pack(side='left', fill='y')
        ttk.Label(text_box, text=title, style='HeroTitle.TLabel').pack(anchor='w', pady=(18, 0))
        ttk.Label(text_box, text=subtitle, style='HeroSub.TLabel').pack(anchor='w', pady=(3, 0))

        status = tk.Frame(header, bg='#0E2032', padx=12, pady=7)
        status.pack(side='right', padx=22)
        tk.Label(status, text='●  SISTEMA ONLINE', bg='#0E2032', fg=self.COLORS['green'], font=('Segoe UI', 9, 'bold')).pack()
        tk.Label(status, text=f'v{VERSAO_INDUSTRIAL.replace("Factory Intelligence", "FI")}', bg='#0E2032', fg=self.COLORS['muted'], font=('Segoe UI', 8)).pack()
        return header

    def _white_card(self, parent, padding=(18, 14)):
        return ttk.Frame(parent, style='Card.TFrame', padding=padding)

    # -------------------------------------------------------------
    # HOME COMPLETAMENTE REDESENHADA
    # -------------------------------------------------------------
    def mostrar_inicio(self):
        self.limpar()
        self.configure(bg=self.COLORS['background'])
        self._header(
            self,
            'PRINCIPIA MINIMA',
            'Factory Intelligence • Otimização de corte, reaproveitamento e aprendizagem operacional',
        )

        shell = ttk.Frame(self, padding=(18, 16))
        shell.pack(fill='both', expand=True)
        shell.columnconfigure(0, weight=0)
        shell.columnconfigure(1, weight=1)
        shell.rowconfigure(0, weight=1)

        sidebar = tk.Frame(shell, bg=self.COLORS['surface'], width=235, highlightthickness=1, highlightbackground=self.COLORS['border'])
        sidebar.grid(row=0, column=0, sticky='nsw', padx=(0, 14))
        sidebar.grid_propagate(False)

        tk.Label(sidebar, text='NAVEGAÇÃO', bg=self.COLORS['surface'], fg=self.COLORS['muted'], font=('Segoe UI', 9, 'bold')).pack(anchor='w', padx=18, pady=(22, 12))

        def nav_button(text, command, primary=False):
            style = 'Accent.TButton' if primary else 'Secondary.TButton'
            b = ttk.Button(sidebar, text=text, style=style, command=command)
            b.pack(fill='x', padx=14, pady=5)
            return b

        nav_button('▸ Planejamento inteligente', self.mostrar_planejado, True)
        nav_button('▸ Modo emergencial', self.mostrar_emergencial)
        nav_button('▸ Histórico de execuções', self.mostrar_historico)
        nav_button('▸ Selecionar logo MR', self.selecionar_logo_mr)

        tk.Frame(sidebar, bg=self.COLORS['border'], height=1).pack(fill='x', padx=16, pady=18)
        tk.Label(sidebar, text='BANCO LOCAL', bg=self.COLORS['surface'], fg=self.COLORS['muted'], font=('Segoe UI', 8, 'bold')).pack(anchor='w', padx=18)
        tk.Label(sidebar, text='SQLite ativo\nModelos usados são validados\npelo operador.', bg=self.COLORS['surface'], fg=self.COLORS['text'], font=('Segoe UI', 9), justify='left').pack(anchor='w', padx=18, pady=(5, 0))

        main = ttk.Frame(shell)
        main.grid(row=0, column=1, sticky='nsew')

        hero = ttk.Frame(main, style='Card.TFrame', padding=(24, 22))
        hero.pack(fill='x', pady=(0, 14))
        ttk.Label(hero, text='CENTRO DE OTIMIZAÇÃO', style='CardTitle.TLabel').pack(anchor='w')
        ttk.Label(hero, text='Escolha a estratégia de produção', style='CardValue.TLabel').pack(anchor='w', pady=(5, 3))
        ttk.Label(
            hero,
            text='O Principia Minima gera o plano; o operador confirma se ele foi realmente executado. Somente os modelos confirmados entram na base de aprendizagem operacional.',
            style='White.TLabel',
            wraplength=920,
            justify='left',
        ).pack(anchor='w', pady=(4, 0))

        cards = ttk.Frame(main)
        cards.pack(fill='both', expand=True)
        cards.columnconfigure(0, weight=1)
        cards.columnconfigure(1, weight=1)
        cards.rowconfigure(0, weight=1)

        specs = [
            (
                'PLANEJAMENTO INTELIGENTE',
                'Demanda futura + Principia Lab. Minimiza barras e desperdício, reduz fragmentação e valoriza retalhos com melhor potencial histórico.',
                'ABRIR PLANEJAMENTO',
                self.mostrar_planejado,
                self.COLORS['cyan'],
            ),
            (
                'MODO EMERGENCIAL',
                'Usa bons padrões dos retalhos existentes primeiro. Quando necessário, libera barras novas do estoque para encontrar uma solução melhor.',
                'ABRIR EMERGENCIAL',
                self.mostrar_emergencial,
                self.COLORS['green'],
            ),
        ]

        for col, (title, desc, button, cmd, accent_color) in enumerate(specs):
            card = tk.Frame(cards, bg=self.COLORS['surface'], highlightthickness=1, highlightbackground=self.COLORS['border'])
            card.grid(row=0, column=col, padx=(0 if col == 0 else 8, 0 if col == 1 else 8), sticky='nsew')
            tk.Frame(card, bg=accent_color, height=4).pack(fill='x')
            inner = tk.Frame(card, bg=self.COLORS['surface'], padx=22, pady=22)
            inner.pack(fill='both', expand=True)
            tk.Label(inner, text=title, bg=self.COLORS['surface'], fg=self.COLORS['white'], font=('Segoe UI Semibold', 15)).pack(anchor='w')
            tk.Label(inner, text=desc, bg=self.COLORS['surface'], fg=self.COLORS['muted'], font=('Segoe UI', 10), wraplength=410, justify='left').pack(anchor='w', pady=(12, 22))
            ttk.Button(inner, text=button, style='Accent.TButton', command=cmd).pack(anchor='w')

        footer = tk.Label(
            self,
            text=f'Principia Minima • {VERSAO_INDUSTRIAL} • SQLite local • validação operacional • histórico de modelos usados',
            anchor='w',
            bg='#0A1725',
            fg=self.COLORS['muted'],
            padx=16,
            pady=8,
            font=('Segoe UI', 9),
        )
        footer.pack(fill='x', side='bottom')

    # -------------------------------------------------------------
    # HISTÓRICO COM CONFIRMAÇÃO DO OPERADOR
    # -------------------------------------------------------------
    def mostrar_historico(self):
        df = ler_historico_execucoes_feedback(400)
        win = tk.Toplevel(self)
        win.title('Principia Minima • Histórico e validação')
        win.geometry('1320x700')
        win.minsize(1040, 580)
        win.configure(bg=self.COLORS['background'])
        self._header(win, 'HISTÓRICO DE OTIMIZAÇÕES', 'Propostas do algoritmo e confirmação de uso real pelo operador')

        content = ttk.Frame(win, padding=(18, 14))
        content.pack(fill='both', expand=True)
        card = ttk.Frame(content, style='Card.TFrame', padding=(14, 12))
        card.pack(fill='both', expand=True)

        cols = (
            'data_hora', 'modo', 'confirmacao_operador', 'horizonte_lab',
            'arquivo_demanda', 'excel_saida'
        )
        labels = {
            'data_hora': 'DATA / HORA',
            'modo': 'MODO',
            'confirmacao_operador': 'USO REAL',
            'horizonte_lab': 'HORIZONTE',
            'arquivo_demanda': 'ARQUIVO DE DEMANDA',
            'excel_saida': 'ARQUIVO DE SAÍDA',
        }
        tree = ttk.Treeview(card, columns=cols, show='headings')
        for c in cols:
            tree.heading(c, text=labels[c])
            width = 145
            if c in {'arquivo_demanda', 'excel_saida'}:
                width = 340
            elif c == 'confirmacao_operador':
                width = 130
            tree.column(c, width=width, anchor='center' if c not in {'arquivo_demanda', 'excel_saida'} else 'w')
        for _, row in df.iterrows():
            tree.insert('', 'end', values=[row.get(c, '') for c in cols])

        vbar = ttk.Scrollbar(card, orient='vertical', command=tree.yview)
        hbar = ttk.Scrollbar(card, orient='horizontal', command=tree.xview)
        tree.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set)
        tree.grid(row=0, column=0, sticky='nsew')
        vbar.grid(row=0, column=1, sticky='ns')
        hbar.grid(row=1, column=0, sticky='ew')
        card.rowconfigure(0, weight=1)
        card.columnconfigure(0, weight=1)

        tk.Label(
            win,
            text='USADO = o operador confirmou execução real. Esses registros alimentam MODELOS_USADOS para análises futuras.',
            anchor='w',
            bg='#0A1725',
            fg=self.COLORS['muted'],
            padx=16,
            pady=8,
            font=('Segoe UI', 9),
        ).pack(fill='x', side='bottom')

    # -------------------------------------------------------------
    # DASHBOARD FINAL + BOTÃO SIM/NÃO DO OPERADOR
    # -------------------------------------------------------------
    def mostrar_resultado(self, modo, resumo, caminho_excel, faltas):
        win = tk.Toplevel(self)
        win.title(f'Principia Minima • Dashboard final • {modo}')
        win.geometry('1390x830')
        win.minsize(1160, 720)
        win.configure(bg=self.COLORS['background'])
        self._header(win, f'DASHBOARD FINAL • {modo}', 'Resultado matemático, documentos operacionais e confirmação de uso real')

        notebook = ttk.Notebook(win)
        notebook.pack(fill='both', expand=True, padx=18, pady=(14, 10))
        dash = ttk.Frame(notebook, padding=12)
        detail = ttk.Frame(notebook, padding=12)
        notebook.add(dash, text='Dashboard')
        notebook.add(detail, text='Detalhamento')

        if modo == 'PLANEJADO' and isinstance(self._ultima_comparacao, pd.DataFrame) and not self._ultima_comparacao.empty:
            comp_tab = ttk.Frame(notebook, padding=12)
            notebook.add(comp_tab, text='Comparação de retalhos')
            self._build_comparison_tab(comp_tab)

        if modo == 'EMERGENCIAL' and isinstance(self._ultimo_estoque_final, pd.DataFrame) and not self._ultimo_estoque_final.empty:
            stock_tab = ttk.Frame(notebook, padding=12)
            notebook.add(stock_tab, text='Estoque final')
            self._build_stock_tab(stock_tab)

        total_fontes = int(resumo['TOTAL_FONTES_USADAS'].sum()) if 'TOTAL_FONTES_USADAS' in resumo.columns else int(resumo.get('BARRAS_NOVAS_USADAS', pd.Series(dtype=float)).sum())
        total_desp = float(resumo['DESPERDICIO_REAL_MM'].sum()) if 'DESPERDICIO_REAL_MM' in resumo.columns else 0.0
        total_ret = float(resumo['RETALHO_REAPROVEITAVEL_MM'].sum()) if 'RETALHO_REAPROVEITAVEL_MM' in resumo.columns else 0.0
        aproveitamento = float(resumo['APROVEITAMENTO_PERCENTUAL'].mean()) if 'APROVEITAMENTO_PERCENTUAL' in resumo.columns and not resumo.empty else 0.0
        faltantes = int(resumo['PECAS_FALTANTES'].sum()) if 'PECAS_FALTANTES' in resumo.columns else 0
        diametros = int(resumo['DIAMETRO'].nunique()) if 'DIAMETRO' in resumo.columns else len(resumo)

        cards = ttk.Frame(dash)
        cards.pack(fill='x')
        values = [
            ('Diâmetros', str(diametros), 'grupos processados'),
            ('Fontes usadas', str(total_fontes), 'barras/retalhos'),
            ('Desperdício total', f'{self._fmt(total_desp)} mm', 'soma consolidada'),
            ('Retalho útil', f'{self._fmt(total_ret)} mm', 'reaproveitável'),
            ('Aproveitamento médio', f'{self._fmt(aproveitamento, 2)}%', 'média por diâmetro'),
            ('Peças faltantes', str(faltantes), '0 = atendimento completo'),
        ]
        for i, item in enumerate(values):
            cards.columnconfigure(i, weight=1)
            self._kpi_card(cards, *item).grid(
                row=0,
                column=i,
                padx=(0 if i == 0 else 5, 0 if i == len(values) - 1 else 5),
                sticky='nsew',
            )

        feedback = tk.Frame(
            dash,
            bg=self.COLORS['surface'],
            highlightthickness=1,
            highlightbackground=self.COLORS['border'],
            padx=18,
            pady=15,
        )
        feedback.pack(fill='x', pady=14)
        tk.Label(
            feedback,
            text='CONFIRMAÇÃO DO OPERADOR',
            bg=self.COLORS['surface'],
            fg=self.COLORS['light_blue'],
            font=('Segoe UI', 9, 'bold'),
        ).pack(anchor='w')
        tk.Label(
            feedback,
            text='Este plano/modelo foi realmente utilizado na produção?',
            bg=self.COLORS['surface'],
            fg=self.COLORS['white'],
            font=('Segoe UI Semibold', 13),
        ).pack(anchor='w', pady=(5, 3))
        tk.Label(
            feedback,
            text='A resposta cria a referência operacional necessária para aprender, no futuro, quais padrões e retalhos realmente funcionam na fábrica.',
            bg=self.COLORS['surface'],
            fg=self.COLORS['muted'],
            font=('Segoe UI', 9),
            wraplength=980,
            justify='left',
        ).pack(anchor='w', pady=(0, 10))

        feedback_status = tk.StringVar(value='Aguardando confirmação do operador')
        buttons = tk.Frame(feedback, bg=self.COLORS['surface'])
        buttons.pack(fill='x')

        def confirmar(usado):
            try:
                status = registrar_feedback_operador(
                    self._ultima_execucao_id,
                    usado,
                    self._ultimo_plano,
                )
                if usado:
                    feedback_status.set('✓ USADO NA PRODUÇÃO • modelo salvo na base validada')
                else:
                    feedback_status.set('✕ NÃO USADO • decisão registrada, modelo não entra na base validada')
                messagebox.showinfo(
                    'Confirmação registrada',
                    f'Execução {self._ultima_execucao_id}\nStatus: {status}',
                    parent=win,
                )
            except Exception as exc:
                messagebox.showerror('Erro ao registrar', str(exc), parent=win)

        ttk.Button(buttons, text='✓ SIM — USEI ESTE PLANO', style='Success.TButton', command=lambda: confirmar(True)).pack(side='left', padx=(0, 8))
        ttk.Button(buttons, text='✕ NÃO — ESTE PLANO NÃO FOI USADO', style='Danger.TButton', command=lambda: confirmar(False)).pack(side='left', padx=8)
        tk.Label(buttons, textvariable=feedback_status, bg=self.COLORS['surface'], fg=self.COLORS['muted'], font=('Segoe UI', 9, 'bold')).pack(side='right')

        progress_card = ttk.Frame(dash, style='Card.TFrame', padding=(18, 15))
        progress_card.pack(fill='x', pady=(0, 14))
        ttk.Label(progress_card, text='PROCESSAMENTO CONCLUÍDO', style='CardTitle.TLabel').pack(anchor='w')
        done = ttk.Progressbar(progress_card, maximum=100, value=100, style='Overall.Horizontal.TProgressbar')
        done.pack(fill='x', pady=(10, 4))
        ttk.Label(progress_card, text='100% • Plano final disponível para análise, validação e impressão', style='MutedWhite.TLabel').pack(anchor='w')

        actions = ttk.Frame(dash)
        actions.pack(fill='x')
        ttk.Button(actions, text='Abrir Excel', style='Accent.TButton', command=lambda: self.abrir_arquivo(caminho_excel)).pack(side='left', padx=(0, 8))
        ttk.Button(actions, text='Plano visual', style='Accent.TButton', command=lambda: mostrar_animacao_corte(self, self._ultimo_plano, self._ultimo_limite_retalho)).pack(side='left', padx=8)
        if self._ultimo_html:
            ttk.Button(actions, text='Folha para imprimir', style='Accent.TButton', command=lambda: webbrowser.open(Path(self._ultimo_html).resolve().as_uri())).pack(side='left', padx=8)
        ttk.Button(actions, text='Abrir pasta', style='Secondary.TButton', command=lambda: self.abrir_pasta(os.path.dirname(caminho_excel))).pack(side='left', padx=8)
        ttk.Button(actions, text='Fechar', style='Secondary.TButton', command=win.destroy).pack(side='right')

        self._build_summary_table(detail, resumo)


# =====================================================================
# EXECUÇÃO V3.2
# =====================================================================
if __name__ == '__main__':
    app = PrincipiaMinimaFactoryApp()
    app.mainloop()
