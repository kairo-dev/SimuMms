# MICROMOUSE - LOGICA DE MOVIMENTO (X TUR)
#
# Codigo no formato em que roda no robo:
#
#   * class Hardware  -> UNICA parte que depende de componentes fisicos
#                        (sensores de parede, motores, chaves seletoras).
#                        No robo real, preencha cada metodo com o seu codigo.
#   * setup()         -> roda uma vez ao ligar / no inicio de cada corrida.
#   * passo()         -> um ciclo: le sensores, decide e comanda UM movimento.
#   * executar()      -> setup() + passo() em loop ate o robo parar.
#
# O robo NAO recebe o mapa do labirinto: ele so tem 3 sensores de parede
# (frente, esquerda, direita). Por isso:
#   RECONHECIMENTO: explora o labirinto e monta o proprio mapa;
#   RAPIDA:         usa o mapa aprendido e segue pelo caminho mais rapido.
# A memoria (M) precisa sobreviver entre as corridas (RAM ligada ou EEPROM/flash):
# o que foi aprendido no reconhecimento e usado na corrida rapida.
#
# Convencao: o robo comeca no quadrado inicial, virado para o NORTE.
#   (x, y) = (0, 0) e o quadrado inicial; x cresce para leste, y para norte.
#   Direcoes: N=0, E=1, S=2, W=3.

import heapq

N, E, S, W = 0, 1, 2, 3
DX = [0, 1, 0, -1]
DY = [1, 0, -1, 0]

RECONHECIMENTO = "reconhecimento"
RAPIDA = "rapida"

# Custos relativos usados so para PLANEJAR o caminho (curva custa tempo, entao
# o caminho com menos curvas pode ser melhor que o mais curto em celulas).
# No robo real, ajuste com os tempos medidos de andar 1 celula e girar 90 graus.
CUSTO_ANDAR = 0.25
CUSTO_GIRO = 0.12


# ============================================================================
#  HARDWARE  (preencher no robo real)
# ============================================================================
class Hardware:
    # ---- entradas ----
    def ler_parede_frente(self):
        """True se ha parede a frente (sensor frontal)."""
        raise NotImplementedError

    def ler_parede_esquerda(self):
        """True se ha parede a esquerda."""
        raise NotImplementedError

    def ler_parede_direita(self):
        """True se ha parede a direita."""
        raise NotImplementedError

    def na_zona_destino(self):
        """True se o robo esta na zona de destino (se o robo tiver como saber)."""
        return False

    def modo_corrida(self):
        """RECONHECIMENTO ou RAPIDA, lido de uma chave seletora do robo."""
        return RECONHECIMENTO

    def tamanho_maze(self):
        """Lado do maze em celulas (6 ou 16), lido de uma chave seletora."""
        return 16

    # ---- saidas (cada uma bloqueia ate o movimento terminar) ----
    def andar_celula(self):
        """Anda uma celula (18 cm) para frente."""
        raise NotImplementedError

    def girar_esquerda(self):
        """Gira 90 graus para a esquerda, parado no lugar."""
        raise NotImplementedError

    def girar_direita(self):
        """Gira 90 graus para a direita, parado no lugar."""
        raise NotImplementedError

    def parar(self):
        """Para os motores por completo."""
        raise NotImplementedError


hw = Hardware()


# ============================================================================
#  MEMORIA
# ============================================================================
M = {}


def resetar_memoria():
    """Apaga o mapa aprendido."""
    M.clear()
    M.update(paredes={}, destino=None, tam=None, modo=RECONHECIMENTO)
    _zerar_pose()


def _zerar_pose():
    M.update(x=0, y=0, h=N, fila=[], volta_aberta=False, no_destino=False)


resetar_memoria()


def setup():
    """Chamar uma vez antes de cada corrida (robo no quadrado inicial)."""
    tam = hw.tamanho_maze()
    if M.get("tam") != tam:
        resetar_memoria()
        M["tam"] = tam
    _zerar_pose()
    M["modo"] = hw.modo_corrida()


# ============================================================================
#  MAPA
# ============================================================================
def _registrar(x, y, h):
    """Le os sensores e guarda as paredes da celula atual no mapa."""
    p = M["paredes"].setdefault((x, y), [None, None, None, None])
    p[h] = hw.ler_parede_frente()
    p[(h + 3) % 4] = hw.ler_parede_esquerda()
    p[(h + 1) % 4] = hw.ler_parede_direita()
    if (x, y) == (0, 0):
        p[S] = True                      # quadrado inicial: 3 lados fechados
    if M["volta_aberta"]:
        p[(h + 2) % 4] = False           # de onde eu vim esta aberto
        M["volta_aberta"] = False
    M["no_destino"] = hw.na_zona_destino()
    if M["no_destino"]:
        M["destino"] = (x, y)


def _parede_conhecida(x, y, d):
    """True/False se ja sei, None se ainda nao sei."""
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
    """Dijkstra sobre (x, y, direcao) usando so o que ja foi mapeado.
    Devolve a lista de acoes ate a celula mais barata que satisfaz eh_alvo."""
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
        viz = [("E", (x, y, (h + 3) % 4), CUSTO_GIRO), ("D", (x, y, (h + 1) % 4), CUSTO_GIRO)]
        if _aberto(x, y, h):
            viz.append(("F", (x + DX[h], y + DY[h], h), CUSTO_ANDAR))
        for a, ne, custo in viz:
            nc = c + custo
            if nc < dist.get(ne, 1e18):
                dist[ne] = nc
                prev[ne] = (e, a)
                heapq.heappush(fila, (nc, ne))
    return None


# ============================================================================
#  DECISAO
# ============================================================================
def _decidir(x, y, h):
    """Devolve 'F' (andar), 'E' (girar esq.), 'D' (girar dir.) ou 'P' (parar)."""
    # corrida rapida com o destino conhecido: segue o plano ideal
    if M["modo"] == RAPIDA:
        if M["no_destino"]:
            return "P"                   # chegou: precisa PARAR por completo
        if M["destino"] is not None:
            if not M["fila"]:
                M["fila"] = _planejar((x, y, h), lambda c: c == M["destino"]) or []
            if M["fila"]:
                return M["fila"].pop(0)
        # sem mapa: explora ate achar o destino (lento, mas valido)

    # exploracao: vai para a celula ainda nao visitada mais "barata"
    visitadas = M["paredes"]
    acoes = _planejar((x, y, h), lambda c: c not in visitadas)
    if acoes:
        return acoes[0]

    # tudo explorado: volta ao inicio e para
    if (x, y) != (0, 0):
        acoes = _planejar((x, y, h), lambda c: c == (0, 0))
        if acoes:
            return acoes[0]
    return "P"


def _executar(acao):
    """Comanda os motores e atualiza a pose estimada (odometria por contagem)."""
    if acao == "F":
        hw.andar_celula()
        M["x"] += DX[M["h"]]
        M["y"] += DY[M["h"]]
        M["volta_aberta"] = True
    elif acao == "D":
        hw.girar_direita()
        M["h"] = (M["h"] + 1) % 4
    elif acao == "E":
        hw.girar_esquerda()
        M["h"] = (M["h"] + 3) % 4
    else:
        hw.parar()


def passo():
    """Um ciclo do robo. Devolve False quando o robo parou."""
    x, y, h = M["x"], M["y"], M["h"]
    _registrar(x, y, h)
    acao = _decidir(x, y, h)
    _executar(acao)
    return acao != "P"


def executar():
    """Programa principal do robo."""
    setup()
    while passo():
        pass


if __name__ == "__main__":
    executar()
