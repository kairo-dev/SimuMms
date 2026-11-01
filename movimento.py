# ALGORITMO DO MICROMOUSE (para o simulador_micromouse.py)
#
# Como o robô "enxerga": SÓ tem 3 sensores de parede (frente, esquerda, direita),
# exatamente como um micromouse de verdade. O mapa NÃO é fornecido (o guia do X TUR
# proíbe passar informações do maze para o robô), então o robô precisa:
#   1) RECONHECIMENTO: explorar o labirinto e montar o próprio mapa;
#   2) CORRIDA RÁPIDA: usar o mapa aprendido e ir pelo caminho mais rápido.
#
# O simulador chama duas funções:
#   iniciar(tipo_corrida, tamanho)  -> no começo de cada corrida (robô no quadrado
#                                      inicial, virado para o NORTE)
#   decidir(sensores)               -> a cada passo; devolve UMA ação:
#         'F' = andar uma célula para frente
#         'E' = girar 90° para a esquerda
#         'D' = girar 90° para a direita
#         'P' = parar (encerra a corrida)
#
# 'sensores' é um dict:
#   frente / esquerda / direita : True se há parede naquele lado
#   no_destino                  : True se o robô está na zona de destino
#   tipo_corrida                : 'reconhecimento' ou 'rapida'
#   tempo_restante              : segundos que ainda restam dos 10 minutos
#
# A memória (M) fica guardada entre as corridas, como numa EEPROM/flash do robô:
# o que foi aprendido no reconhecimento é usado na corrida rápida.

import heapq

N, E, S, W = 0, 1, 2, 3
DX = [0, 1, 0, -1]
DY = [1, 0, -1, 0]

# Custos usados só para PLANEJAR (curvas custam tempo, então o caminho
# com menos curvas pode ser melhor que o mais curto em células).
T_ANDAR = 0.25
T_GIRO = 0.12

M = {}


def resetar_memoria():
    """Apaga o mapa aprendido (o simulador chama ao criar um novo maze)."""
    M.clear()
    M.update(paredes={}, destino=None, tam=None)
    _zerar_pose()


def _zerar_pose():
    M.update(x=0, y=0, h=N, fila=[], volta_aberta=False)


resetar_memoria()


def iniciar(tipo_corrida, tamanho):
    if M.get("tam") != tamanho:
        resetar_memoria()
        M["tam"] = tamanho
    _zerar_pose()
    M["tipo"] = tipo_corrida


# ------------------------------------------------------------------ mapa

def _registrar(x, y, h, s):
    p = M["paredes"].setdefault((x, y), [None, None, None, None])
    p[h] = s["frente"]
    p[(h + 3) % 4] = s["esquerda"]
    p[(h + 1) % 4] = s["direita"]
    if (x, y) == (0, 0):
        p[S] = True                      # quadrado inicial: 3 lados fechados
    if M["volta_aberta"]:
        p[(h + 2) % 4] = False           # de onde eu vim está aberto
        M["volta_aberta"] = False
    if s.get("no_destino"):
        M["destino"] = (x, y)


def _parede_conhecida(x, y, d):
    """True/False se já sei, None se ainda não sei."""
    p = M["paredes"].get((x, y))
    if p is not None and p[d] is not None:
        return p[d]
    q = M["paredes"].get((x + DX[d], y + DY[d]))
    if q is not None and q[(d + 2) % 4] is not None:
        return q[(d + 2) % 4]
    return None


def _aberto(x, y, d):
    n = M["tam"]
    nx, ny = x + DX[d], y + DY[d]
    return 0 <= nx < n and 0 <= ny < n and _parede_conhecida(x, y, d) is False


def _planejar(origem, eh_alvo):
    """Dijkstra sobre (x, y, direção) usando só o que já foi mapeado.
    Devolve a lista de ações até a célula mais barata que satisfaz eh_alvo."""
    x0, y0, _ = origem
    dist = {origem: 0.0}
    prev = {}
    fila = [(0.0, origem)]
    while fila:
        c, e = heapq.heappop(fila)
        if c > dist[e]:
            continue
        x, y, h = e
        if (x, y) != (x0, y0) and eh_alvo((x, y)):
            acoes = []
            while e in prev:
                e, a = prev[e]
                acoes.append(a)
            return acoes[::-1]
        viz = [("E", (x, y, (h + 3) % 4), T_GIRO), ("D", (x, y, (h + 1) % 4), T_GIRO)]
        if _aberto(x, y, h):
            viz.append(("F", (x + DX[h], y + DY[h], h), T_ANDAR))
        for a, ne, custo in viz:
            nc = c + custo
            if nc < dist.get(ne, 1e18):
                dist[ne] = nc
                prev[ne] = (e, a)
                heapq.heappush(fila, (nc, ne))
    return None


# ------------------------------------------------------------------ decisão

def _executar(acao):
    """Atualiza a pose estimada (odometria) e devolve a ação."""
    if acao == "F":
        M["x"] += DX[M["h"]]
        M["y"] += DY[M["h"]]
        M["volta_aberta"] = True
    elif acao == "D":
        M["h"] = (M["h"] + 1) % 4
    elif acao == "E":
        M["h"] = (M["h"] + 3) % 4
    return acao


def decidir(s):
    x, y, h = M["x"], M["y"], M["h"]
    _registrar(x, y, h, s)
    tipo = s["tipo_corrida"]

    # --- corrida rápida com o destino já conhecido: segue o plano ótimo
    if tipo == "rapida":
        if s.get("no_destino"):
            return "P"                   # chegou: tem que PARAR por completo
        if M["destino"] is not None:
            if not M["fila"]:
                M["fila"] = _planejar((x, y, h), lambda c: c == M["destino"]) or []
            if M["fila"]:
                return _executar(M["fila"].pop(0))
        # sem mapa: explora até achar o destino (corrida lenta, mas válida)

    # --- exploração: vai até a célula ainda não visitada mais "barata"
    visitadas = M["paredes"]
    acoes = _planejar((x, y, h), lambda c: c not in visitadas)
    if acoes:
        return _executar(acoes[0])

    # --- tudo explorado: volta ao início e para
    if (x, y) != (0, 0):
        acoes = _planejar((x, y, h), lambda c: c == (0, 0))
        if acoes:
            return _executar(acoes[0])
    return "P"
