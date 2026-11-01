# -*- coding: utf-8 -*-
"""
SIMULADOR MICROMOUSE - baseado no Guia de Projeto do X TUR (UFU), secao 6.

O que do guia esta reproduzido aqui
-----------------------------------
* Maze formado por quadrados de 18 cm; paredes de 1,5 cm de espessura e 6 cm de
  altura; postes (pontos de rede) de 1,5 x 1,5 cm nos cantos e pelo menos UMA
  parede em cada ponto de intersecao; parede externa fechando tudo.
* Laterais das paredes brancas, TOPO VERMELHO, piso PRETO (visao de cima).
* Classificatoria = maze 6x6; Final = maze 16x16.
* Quadrado de inicio no canto inferior esquerdo, fechado em 3 lados, com uma unica
  saida. A linha de partida fica entre o quadrado inicial e o adjacente; o
  cronometro comeca quando o robo a cruza.
* Destino ESCONDIDO do robo, posicionado de modo que quem segue parede (mao
  esquerda ou direita) nao o encontra. Existem multiplos caminhos.
* Dois tipos de corrida:
    - RECONHECIMENTO: explora/mapeia, pode passar do destino e voltar ao inicio;
      o tempo NAO conta.
    - RAPIDA: tempo medido da linha de partida ate o destino; so e valida se o
      robo PARAR completamente dentro do destino. Continuar andando, parar fora
      ou voltar ao quadrado inicial invalida a corrida.
* 10 minutos de acesso ao maze (reconhecimentos + rapidas + ajustes).
* Retirar o robo no meio de uma corrida (antes de alcancar o destino) soma
  +15 s ao tempo da proxima corrida rapida valida (penalidades acumulam).
* Tempo oficial = menor tempo entre as corridas rapidas validas. Desempate: mais
  corridas rapidas validas, depois menor media.
* O robo NAO recebe o mapa: so enxerga as paredes a frente/esquerda/direita.

Controles:  R reconhecimento | F corrida rapida | ESPACO pausa | X retirar robo
            N novo maze | T troca fase (6x6 / 16x16) | G mostra/oculta destino
            V mapa explorado | + / - velocidade | ESC sai

O codigo do robo (movimento.py) roda aqui exatamente como no robo: ele so usa a
classe Hardware (sensores de parede, motores, chaves). O simulador fornece um
HardwareSimulado no lugar do hardware real.

Uso:  python simulador_micromouse.py [--movimento modulo] [--fase final]
                                     [--semente 123] [--teste 5]
"""

import sys
import math
import random
import heapq
import argparse
import importlib
import traceback
from collections import deque

# ----------------------------------------------------------------------------
# Especificacoes oficiais (guia, secao 6)
# ----------------------------------------------------------------------------
CELULA_CM = 18.0
ESPESSURA_CM = 1.5
ALTURA_PAREDE_CM = 6.0
ROBO_MAX_CM = 16.0
TEMPO_ACESSO_S = 600.0              # 10 minutos
PENALIDADE_REPOSICIONAMENTO_S = 15.0
TAMANHOS = {"classificatoria": 6, "final": 16}
NOMES_FASE = {"classificatoria": "Classificatória 6x6", "final": "Final 16x16"}

# Modelo de tempo do robo simulado (segundos simulados por acao)
T_ANDAR = 0.25
T_GIRO = 0.12
T_BATIDA = 0.30

# O guia nao diz como o robo "sabe" que chegou ao destino (o sensor de chegada
# e do sistema de cronometragem). Aqui o robo recebe um sensor 'no_destino'.
# Ponha False para o robo ficar totalmente cego quanto ao destino.
SENSOR_DESTINO = True

N, E, S, W = 0, 1, 2, 3
DX = [0, 1, 0, -1]
DY = [1, 0, -1, 0]


# ----------------------------------------------------------------------------
# Labirinto
# ----------------------------------------------------------------------------
class Labirinto:
    """Paredes guardadas como segmentos entre pontos de rede.

    hw[x][y] : segmento horizontal na linha de rede y, entre os pontos x e x+1
               (parede ao sul da celula (x,y) e ao norte da (x,y-1)).
    vw[x][y] : segmento vertical na coluna de rede x, entre os pontos y e y+1
               (parede a oeste da celula (x,y) e a leste da (x-1,y)).
    Coordenadas: x cresce para leste, y cresce para NORTE; (0,0) = canto
    inferior esquerdo = quadrado inicial.
    """

    def __init__(self, n):
        self.n = n
        self.hw = [[True] * (n + 1) for _ in range(n)]
        self.vw = [[True] * n for _ in range(n + 1)]
        self.destino = None

    # -- acesso -------------------------------------------------------------
    def parede(self, x, y, d):
        if d == N:
            return self.hw[x][y + 1]
        if d == S:
            return self.hw[x][y]
        if d == E:
            return self.vw[x + 1][y]
        return self.vw[x][y]

    def _set(self, x, y, d, v):
        if d == N:
            self.hw[x][y + 1] = v
        elif d == S:
            self.hw[x][y] = v
        elif d == E:
            self.vw[x + 1][y] = v
        else:
            self.vw[x][y] = v

    def dentro(self, x, y):
        return 0 <= x < self.n and 0 <= y < self.n

    def paredes_no_ponto(self, px, py):
        n, c = self.n, 0
        if px >= 1 and self.hw[px - 1][py]:
            c += 1
        if px <= n - 1 and self.hw[px][py]:
            c += 1
        if py >= 1 and self.vw[px][py - 1]:
            c += 1
        if py <= n - 1 and self.vw[px][py]:
            c += 1
        return c

    # -- geracao ------------------------------------------------------------
    def _carvar(self, rng):
        n = self.n
        vis = [[False] * n for _ in range(n)]
        vis[0][0] = True                    # inicio: so a saida norte
        self._set(0, 0, N, False)
        vis[0][1] = True
        pilha = [(0, 1)]
        while pilha:
            x, y = pilha[-1]
            viz = [d for d in range(4)
                   if self.dentro(x + DX[d], y + DY[d]) and not vis[x + DX[d]][y + DY[d]]]
            if not viz:
                pilha.pop()
                continue
            d = rng.choice(viz)
            self._set(x, y, d, False)
            nx, ny = x + DX[d], y + DY[d]
            vis[nx][ny] = True
            pilha.append((nx, ny))

    def _paredes_removiveis(self):
        n, c = self.n, []
        for x in range(n):
            for y in range(1, n):
                if self.hw[x][y]:
                    c.append(("h", x, y))
        for x in range(1, n):
            for y in range(n):
                if self.vw[x][y] and not (x == 1 and y == 0):   # lado leste do inicio
                    c.append(("v", x, y))
        return c

    def _remover(self, tipo, x, y):
        """Remove uma parede interna (cria caminho alternativo) sem deixar
        nenhum ponto de rede sem parede."""
        arr = self.hw if tipo == "h" else self.vw
        arr[x][y] = False
        pts = [(x, y), (x + 1, y)] if tipo == "h" else [(x, y), (x, y + 1)]
        if any(self.paredes_no_ponto(px, py) == 0 for px, py in pts):
            arr[x][y] = True
            return False
        return True

    def distancias(self):
        dist = {(0, 0): 0}
        fila = deque([(0, 0)])
        while fila:
            x, y = fila.popleft()
            for d in range(4):
                if not self.parede(x, y, d):
                    c = (x + DX[d], y + DY[d])
                    if c not in dist:
                        dist[c] = dist[(x, y)] + 1
                        fila.append(c)
        return dist

    def seguidor_de_parede(self, mao):
        """Celulas visitadas por um robo que segue a parede (mao=-1 esquerda,
        +1 direita) a partir do inicio."""
        x = y = h = 0
        vis = {(0, 0)}
        for _ in range(self.n * self.n * 16):
            for giro in (mao, 0, -mao, 2):
                d = (h + giro) % 4
                if not self.parede(x, y, d):
                    h = d
                    x += DX[d]
                    y += DY[d]
                    break
            vis.add((x, y))
        return vis

    def _escolher_destino(self, rng):
        n = self.n
        vis = self.seguidor_de_parede(-1) | self.seguidor_de_parede(1)
        dist = self.distancias()
        dmin = max(3, int(n * 0.8))
        cand = [(x, y) for x in range(n) for y in range(n)
                if (x, y) not in vis and dist.get((x, y), 0) >= dmin]
        if not cand:
            return None
        cand.sort(key=lambda c: -dist[c])
        return rng.choice(cand[:max(1, len(cand) // 2)])


def criar_labirinto(n, rng):
    for _ in range(500):
        lab = Labirinto(n)
        lab._carvar(rng)
        rem = lab._paredes_removiveis()
        rng.shuffle(rem)
        i = 0
        for _ in range(int(len(rem) * (0.10 if n > 8 else 0.08))):
            lab._remover(*rem[i])
            i += 1
        while i < len(rem) * 0.45:
            dest = lab._escolher_destino(rng)
            if dest:
                lab.destino = dest
                return lab
            lab._remover(*rem[i])
            i += 1
    raise RuntimeError("Nao consegui gerar um maze valido")


def tempo_otimo(lab):
    """Menor tempo (modelo T_ANDAR/T_GIRO) do inicio ao destino - so p/ conferencia."""
    ini = (0, 0, N)
    dist = {ini: 0.0}
    fila = [(0.0, ini)]
    while fila:
        c, e = heapq.heappop(fila)
        if c > dist[e]:
            continue
        x, y, h = e
        if (x, y) == lab.destino:
            return c
        viz = [((x, y, (h + 1) % 4), T_GIRO), ((x, y, (h + 3) % 4), T_GIRO)]
        if not lab.parede(x, y, h):
            viz.append(((x + DX[h], y + DY[h], h), T_ANDAR))
        for ne, custo in viz:
            if c + custo < dist.get(ne, 1e18):
                dist[ne] = c + custo
                heapq.heappush(fila, (c + custo, ne))
    return None


# ----------------------------------------------------------------------------
# Hardware simulado (substitui movimento.Hardware)
# ----------------------------------------------------------------------------
class HardwareSimulado:
    def __init__(self, sim):
        self.sim = sim
        self.modo = "reconhecimento"
        self.pedido = None              # ultima acao comandada pelo robo

    def ler_parede_frente(self):
        s = self.sim
        return s.lab.parede(s.x, s.y, s.h)

    def ler_parede_esquerda(self):
        s = self.sim
        return s.lab.parede(s.x, s.y, (s.h + 3) % 4)

    def ler_parede_direita(self):
        s = self.sim
        return s.lab.parede(s.x, s.y, (s.h + 1) % 4)

    def na_zona_destino(self):
        s = self.sim
        return SENSOR_DESTINO and (s.x, s.y) == s.lab.destino

    def modo_corrida(self):
        return self.modo

    def tamanho_maze(self):
        return self.sim.n

    def andar_celula(self):
        self.pedido = "F"

    def girar_esquerda(self):
        self.pedido = "E"

    def girar_direita(self):
        self.pedido = "D"

    def parar(self):
        self.pedido = "P"


# ----------------------------------------------------------------------------
# Simulacao (logica, sem pygame)
# ----------------------------------------------------------------------------
class Simulacao:
    def __init__(self, mov, fase="classificatoria", semente=None):
        self.mov = mov
        self.hw = HardwareSimulado(self)
        self.mov.hw = self.hw           # o robo passa a usar o hardware simulado
        self.fase = fase
        self.vel = 4.0
        self.pausado = False
        self.nova_sessao(semente)

    def nova_sessao(self, semente=None):
        self.semente = semente if semente is not None else random.randrange(10 ** 6)
        self.n = TAMANHOS[self.fase]
        self.lab = criar_labirinto(self.n, random.Random(self.semente))
        if hasattr(self.mov, "resetar_memoria"):
            self.mov.resetar_memoria()
        self.tempo_restante = TEMPO_ACESSO_S
        self.fim = False
        self.corrida = None
        self.acao = None
        self.x = self.y = self.h = 0
        self.visitadas = {(0, 0)}
        self.trilha = [(0, 0)]
        self.tempos_validos = []
        self.rapidas_invalidas = 0
        self.n_recon = 0
        self.penalidades = 0           # numero de reposicionamentos pendentes
        self.destino_visto = False
        self.log = []
        self._log("Maze %s gerado (semente %d). Destino escondido do robô."
                  % (NOMES_FASE[self.fase], self.semente))

    def _log(self, msg):
        self.log.append(msg)
        self.log = self.log[-40:]
        print(msg)

    # -- estatisticas ---------------------------------------------------------
    @property
    def melhor(self):
        return min(self.tempos_validos) if self.tempos_validos else None

    @property
    def media(self):
        return sum(self.tempos_validos) / len(self.tempos_validos) if self.tempos_validos else None

    # -- comandos -------------------------------------------------------------
    def iniciar_corrida(self, tipo):
        if self.corrida or self.fim:
            return
        self.x = self.y = self.h = 0
        self.acao = None
        self.trilha = [(0, 0)]
        self.corrida = dict(tipo=tipo, t=0.0, cron=False, chegou=False, t_chegada=None, batidas=0)
        try:
            self.hw.modo = tipo
            self.mov.setup()
        except Exception:
            traceback.print_exc()
            self._encerrar_invalida("Erro em movimento.setup() (veja o terminal).")
            return
        self._log("Corrida de %s iniciada." % ("reconhecimento" if tipo == "reconhecimento" else "RÁPIDA"))

    def retirar_robo(self):
        """Operador pega o robo no meio da corrida e o recoloca no inicio."""
        c = self.corrida
        if not c:
            return
        if not c["chegou"]:
            self.penalidades += 1
            self._log("Robô retirado antes do destino: +%d s na próxima rápida válida."
                      % (self.penalidades * PENALIDADE_REPOSICIONAMENTO_S))
        else:
            self._log("Robô retirado (destino já alcançado, sem penalidade).")
        if c["tipo"] == "rapida":
            self.rapidas_invalidas += 1
        self._resetar_robo()

    def _resetar_robo(self):
        self.corrida = None
        self.acao = None
        self.x = self.y = self.h = 0

    # -- passo da simulacao ---------------------------------------------------
    def _proxima_acao(self):
        c, lab = self.corrida, self.lab
        self.hw.pedido = None
        try:
            self.mov.passo()
        except Exception:
            traceback.print_exc()
            self._encerrar_invalida("Erro em movimento.passo() (veja o terminal).")
            return
        a = self.hw.pedido
        if a not in ("F", "E", "D", "P"):
            self._encerrar_invalida("O robô não comandou nenhum movimento em passo().")
            return
        if a == "P":
            self._parar()
            return
        if c["tipo"] == "rapida" and c["chegou"]:
            self._encerrar_invalida("Inválida: o robô continuou se movendo após chegar ao destino.")
            return
        if a == "F":
            if lab.parede(self.x, self.y, self.h):
                c["batidas"] += 1
                self.acao = dict(tipo="B", custo=T_BATIDA, prog=0.0)
            else:
                self.acao = dict(tipo="F", custo=T_ANDAR, prog=0.0,
                                 inicia_cron=(not c["cron"] and (self.x, self.y) == (0, 0) and self.h == N))
        else:
            self.acao = dict(tipo=a, custo=T_GIRO, prog=0.0)

    def _avancar_acao(self, d):
        c, a = self.corrida, self.acao
        if a.get("inicia_cron") and not c["cron"]:
            meia = a["custo"] / 2.0          # linha de partida = meio do caminho
            depois = a["prog"] + d
            if depois >= meia:
                c["cron"] = True
                c["t"] += depois - max(a["prog"], meia)
        elif c["cron"] and not c["chegou"]:
            c["t"] += d
        a["prog"] += d
        self.tempo_restante -= d

    def _concluir_acao(self):
        a, c, lab = self.acao, self.corrida, self.lab
        self.acao = None
        if a["tipo"] == "F":
            self.x += DX[self.h]
            self.y += DY[self.h]
            self.visitadas.add((self.x, self.y))
            self.trilha.append((self.x, self.y))
        elif a["tipo"] == "E":
            self.h = (self.h + 3) % 4
        elif a["tipo"] == "D":
            self.h = (self.h + 1) % 4
        if (self.x, self.y) == lab.destino and not c["chegou"]:
            c["chegou"] = True
            c["t_chegada"] = c["t"]
            self.destino_visto = True
            if c["tipo"] == "rapida":
                self._log("Destino alcançado em %.3f s - o robô precisa PARAR agora." % c["t"])
            else:
                self._log("Destino encontrado no reconhecimento (tempo não conta).")
        if (c["tipo"] == "rapida" and c["cron"] and a["tipo"] == "F"
                and (self.x, self.y) == (0, 0)):
            self._encerrar_invalida("Inválida: o robô voltou ao quadrado inicial antes de concluir.")

    def _parar(self):
        c = self.corrida
        pos = (self.x, self.y)
        if c["tipo"] == "reconhecimento":
            self.n_recon += 1
            self._log("Reconhecimento encerrado (%d células exploradas)." % len(self.visitadas))
            self._resetar_robo()
            return
        if not c["cron"]:
            self._encerrar_invalida("Inválida: parou antes de cruzar a linha de partida.")
        elif pos == self.lab.destino and c["chegou"]:
            oficial = c["t_chegada"] + self.penalidades * PENALIDADE_REPOSICIONAMENTO_S
            self.tempos_validos.append(oficial)
            extra = (" (inclui +%d s de penalidade)" % (self.penalidades * PENALIDADE_REPOSICIONAMENTO_S)
                     if self.penalidades else "")
            self._log("CORRIDA RÁPIDA VÁLIDA: %.3f s%s" % (oficial, extra))
            self.penalidades = 0
            self._resetar_robo()
        else:
            self.penalidades += 1
            self._encerrar_invalida("Inválida: o robô parou fora do destino (+15 s por reposicionar).")

    def _encerrar_invalida(self, motivo):
        if self.corrida and self.corrida["tipo"] == "rapida":
            self.rapidas_invalidas += 1
        self._log(motivo)
        self._resetar_robo()

    def atualizar(self, dt):
        """Avanca a simulacao dt segundos reais (multiplicado por self.vel)."""
        if self.pausado or not self.corrida or self.fim:
            return
        resto = dt * self.vel
        guarda = 0
        while resto > 1e-9 and self.corrida and guarda < 200000:
            guarda += 1
            if self.acao is None:
                self._proxima_acao()
                if self.acao is None:
                    continue
            falta = self.acao["custo"] - self.acao["prog"]
            passo = min(resto, falta, max(self.tempo_restante, 0.0))
            self._avancar_acao(passo)
            resto -= passo
            if self.tempo_restante <= 1e-9:
                self.tempo_restante = 0.0
                self.fim = True
                self._encerrar_invalida("Tempo de acesso esgotado (10 min).")
                self._log(self.resultado_final())
                return
            if self.acao["prog"] >= self.acao["custo"] - 1e-12:
                self._concluir_acao()

    def resultado_final(self):
        if self.tempos_validos:
            return "Classificado: tempo oficial %.3f s (%d corridas rápidas válidas)." % (
                self.melhor, len(self.tempos_validos))
        return "Sem corrida rápida válida: equipe desclassificada da progressão."

    # -- util para a interface ------------------------------------------------
    def pose_visual(self):
        """(x, y, direcao em quartos de volta) interpolados pela acao atual."""
        x, y, h = float(self.x), float(self.y), float(self.h)
        a = self.acao
        if a:
            f = min(1.0, a["prog"] / a["custo"])
            if a["tipo"] == "F":
                x += DX[self.h] * f
                y += DY[self.h] * f
            elif a["tipo"] == "D":
                h += f
            elif a["tipo"] == "E":
                h -= f
            elif a["tipo"] == "B":                  # "tranco" ao bater na parede
                k = math.sin(f * math.pi) * 0.08
                x += DX[self.h] * k
                y += DY[self.h] * k
        return x, y, h

    def tempo_corrida(self):
        """Cronometro exibido (inclui a fracao da acao em andamento)."""
        c = self.corrida
        if not c:
            return None
        t = c["t"]
        a = self.acao
        if a and c["cron"] and not c["chegou"] and not a.get("inicia_cron"):
            t += a["prog"]
        return t


# ----------------------------------------------------------------------------
# Modo de teste (sem janela)
# ----------------------------------------------------------------------------
def modo_teste(mov, quantos, semente0):
    print("\n=== TESTE SEM JANELA: reconhecimento + corrida rápida ===")
    ok = 0
    total = 0
    for fase in ("classificatoria", "final"):
        for i in range(quantos):
            sim = Simulacao(mov, fase, semente0 + i)
            sim.log = []
            otimo = tempo_otimo(sim.lab)
            for tipo in ("reconhecimento", "rapida"):
                sim.iniciar_corrida(tipo)
                while sim.corrida and not sim.fim:
                    sim.atualizar(5.0)
            total += 1
            if sim.tempos_validos:
                # tempo oficial desconta a meia-celula antes da linha de partida
                esperado = otimo - T_ANDAR / 2.0
                bate = abs(sim.tempos_validos[0] - esperado) < 1e-6
                ok += bate
                print("  %-16s semente %-4d recon: %5.1fs restantes  rápida: %.3f s  ótimo: %.3f s  %s"
                      % (NOMES_FASE[fase], sim.semente, sim.tempo_restante,
                         sim.tempos_validos[0], esperado, "OK" if bate else "(não é o ótimo)"))
            else:
                print("  %-16s semente %-4d SEM corrida válida" % (NOMES_FASE[fase], sim.semente))
    print("Resultado: %d/%d com tempo ótimo.\n" % (ok, total))


# ----------------------------------------------------------------------------
# Interface (pygame)
# ----------------------------------------------------------------------------
C_FUNDO = (24, 26, 32)
C_PISO = (12, 12, 12)
C_GRADE = (30, 30, 30)
C_TOPO = (205, 32, 32)
C_BRANCO = (235, 235, 235)
C_INICIO = (40, 200, 90)
C_DESTINO = (255, 210, 0)
C_ROBO = (50, 110, 255)
C_EXPLORADO = (18, 34, 70)
C_PAINEL = (36, 39, 48)
C_TEXTO = (230, 232, 238)
C_TEXTO_FRACO = (150, 156, 170)
C_BOTAO = (62, 68, 84)
C_BOTAO_OFF = (44, 47, 58)
C_OK = (90, 220, 120)
C_ERRO = (255, 110, 110)

VELOCIDADES = [1, 2, 4, 8, 16, 50, 200]
LADO_MAZE = 720
LARG_TELA, ALT_TELA = 1060, 760
PX = 760                       # x do painel


def fmt_mmss(t):
    t = max(0, int(math.ceil(t)))
    return "%d:%02d" % (t // 60, t % 60)


class Interface:
    def __init__(self, sim):
        import pygame
        self.pg = pygame
        pygame.init()
        self.sim = sim
        self.tela = pygame.display.set_mode((LARG_TELA, ALT_TELA))
        pygame.display.set_caption("Micromouse (X TUR)")
        self.f_peq = pygame.font.Font(None, 21)
        self.f_med = pygame.font.Font(None, 26)
        self.f_gra = pygame.font.Font(None, 56)
        self.f_tit = pygame.font.Font(None, 32)
        self.mostrar_destino = True
        self.mostrar_explorado = True
        self.vel_idx = VELOCIDADES.index(int(sim.vel)) if int(sim.vel) in VELOCIDADES else 2
        self.botoes = []
        self._montar_botoes()
        self._layout()

    # -- layout ----------------------------------------------------------------
    def _layout(self):
        n = self.sim.n
        self.cs = LADO_MAZE // n
        self.ox = 20 + (LADO_MAZE - self.cs * n) // 2
        self.oy = 20 + (LADO_MAZE - self.cs * n) // 2
        self.tw = max(3, int(round(self.cs * ESPESSURA_CM / CELULA_CM)))

    def _montar_botoes(self):
        pg = self.pg
        larg, alt, gap = 135, 36, 10
        y0 = ALT_TELA - 20 - 5 * (alt + gap) + gap
        defs = [
            ("recon", "Reconhecimento (R)"), ("rapida", "Corrida rápida (F)"),
            ("pausa", "Pausar (Espaço)"), ("retirar", "Retirar robô (X)"),
            ("novo", "Novo maze (N)"), ("fase", "Fase (T)"),
            ("vel-", "Velocidade  -"), ("vel+", "Velocidade  +"),
            ("destino", "Destino (G)"), ("explorado", "Explorado (V)"),
        ]
        self.botoes = []
        for i, (bid, _) in enumerate(defs):
            r = pg.Rect(PX + (i % 2) * (larg + gap), y0 + (i // 2) * (alt + gap), larg, alt)
            self.botoes.append((bid, r))
        self.rotulos = dict(defs)

    # -- acoes -----------------------------------------------------------------
    def acao(self, bid):
        sim = self.sim
        if bid == "recon":
            sim.iniciar_corrida("reconhecimento")
        elif bid == "rapida":
            sim.iniciar_corrida("rapida")
        elif bid == "pausa":
            sim.pausado = not sim.pausado
        elif bid == "retirar":
            sim.retirar_robo()
        elif bid == "novo":
            sim.nova_sessao()
        elif bid == "fase":
            sim.fase = "final" if sim.fase == "classificatoria" else "classificatoria"
            sim.nova_sessao()
            self._layout()
        elif bid == "vel+":
            self.vel_idx = min(len(VELOCIDADES) - 1, self.vel_idx + 1)
        elif bid == "vel-":
            self.vel_idx = max(0, self.vel_idx - 1)
        elif bid == "destino":
            self.mostrar_destino = not self.mostrar_destino
        elif bid == "explorado":
            self.mostrar_explorado = not self.mostrar_explorado
        sim.vel = float(VELOCIDADES[self.vel_idx])

    TECLAS = {"r": "recon", "f": "rapida", " ": "pausa", "x": "retirar", "n": "novo",
              "t": "fase", "g": "destino", "v": "explorado", "+": "vel+", "=": "vel+",
              "-": "vel-", "_": "vel-"}

    def _habilitado(self, bid):
        sim = self.sim
        if bid in ("recon", "rapida"):
            return not sim.corrida and not sim.fim
        if bid == "retirar":
            return sim.corrida is not None
        return True

    # -- desenho do maze ---------------------------------------------------------
    def _celula_rect(self, x, y):
        return self.pg.Rect(self.ox + x * self.cs, self.oy + (self.sim.n - 1 - y) * self.cs,
                            self.cs, self.cs)

    def _desenhar_maze(self):
        pg, s, sim, cs, tw = self.pg, self.tela, self.sim, self.cs, self.tw
        n, lab = sim.n, sim.lab
        X = lambda px: self.ox + px * cs
        Y = lambda py: self.oy + (n - py) * cs
        pg.draw.rect(s, C_PISO, (self.ox, self.oy, cs * n, cs * n))
        if self.mostrar_explorado:
            for (x, y) in sim.visitadas:
                pg.draw.rect(s, C_EXPLORADO, self._celula_rect(x, y))
        for i in range(n + 1):
            pg.draw.line(s, C_GRADE, (X(i), Y(0)), (X(i), Y(n)))
            pg.draw.line(s, C_GRADE, (X(0), Y(i)), (X(n), Y(i)))
        # quadrado de inicio e destino
        sup = pg.Surface((cs, cs), pg.SRCALPHA)
        sup.fill((*C_INICIO, 70))
        s.blit(sup, self._celula_rect(0, 0))
        if self.mostrar_destino and lab.destino:
            sup.fill((*C_DESTINO, 120))
            r = self._celula_rect(*lab.destino)
            s.blit(sup, r)
            pg.draw.rect(s, C_DESTINO, r, 2)
            t = self.f_peq.render("META", True, (30, 30, 30))
            s.blit(t, t.get_rect(center=r.center))
        # linha de partida (entre o quadrado inicial e o adjacente)
        pg.draw.line(s, C_INICIO, (X(0) + tw // 2 + 1, Y(1)), (X(1) - tw // 2 - 1, Y(1)), 3)
        t = self.f_peq.render("INÍCIO", True, C_INICIO)
        s.blit(t, t.get_rect(center=(X(0) + cs // 2, Y(0) - cs // 4)))
        # trilha da corrida atual
        if sim.corrida and len(sim.trilha) > 1:
            cor = (0, 230, 255) if sim.corrida["tipo"] == "rapida" else (90, 150, 255)
            pts = [(self._celula_rect(x, y).centerx, self._celula_rect(x, y).centery)
                   for x, y in sim.trilha]
            pg.draw.lines(s, cor, False, pts, 2)
        # paredes (topo vermelho) e postes
        for x in range(n):
            for y in range(n + 1):
                if lab.hw[x][y]:
                    pg.draw.rect(s, C_TOPO, (X(x) - tw // 2, Y(y) - tw // 2, cs + tw, tw))
        for x in range(n + 1):
            for y in range(n):
                if lab.vw[x][y]:
                    pg.draw.rect(s, C_TOPO, (X(x) - tw // 2, Y(y + 1) - tw // 2, tw, cs + tw))
        for px in range(n + 1):
            for py in range(n + 1):
                pg.draw.rect(s, C_TOPO, (X(px) - tw // 2, Y(py) - tw // 2, tw, tw))
        # robo
        self._desenhar_robo()

    def _desenhar_robo(self):
        pg, s, sim, cs = self.pg, self.tela, self.sim, self.cs
        fx, fy, hv = sim.pose_visual()
        cx = self.ox + (fx + 0.5) * cs
        cy = self.oy + (sim.n - 0.5 - fy) * cs
        # sensores (raios ate a parede da celula atual)
        if sim.corrida:
            for giro in (3, 0, 1):
                d = (sim.h + giro) % 4
                if sim.lab.parede(sim.x, sim.y, d):
                    ex = cx + DX[d] * (cs / 2 - self.tw / 2)
                    ey = cy - DY[d] * (cs / 2 - self.tw / 2)
                    pg.draw.line(s, (255, 120, 120), (cx, cy), (ex, ey), 1)
        b = max(8, int(cs * ROBO_MAX_CM / CELULA_CM * 0.92))
        corpo = pg.Surface((b, b), pg.SRCALPHA)
        pg.draw.rect(corpo, C_ROBO, (0, 0, b, b), border_radius=max(2, b // 6))
        pg.draw.rect(corpo, (20, 30, 60), (0, int(b * 0.2), max(2, b // 8), int(b * 0.35)))
        pg.draw.rect(corpo, (20, 30, 60), (b - max(2, b // 8), int(b * 0.2), max(2, b // 8), int(b * 0.35)))
        pg.draw.rect(corpo, (255, 235, 90), (int(b * 0.2), 0, int(b * 0.6), max(2, b // 7)))
        for fxp in (0.2, 0.5, 0.8):
            pg.draw.circle(corpo, (255, 90, 90), (int(b * fxp), max(2, b // 7) + 3), max(1, b // 14))
        corpo = pg.transform.rotate(corpo, -90.0 * hv)
        s.blit(corpo, corpo.get_rect(center=(int(cx), int(cy))))

    # -- painel ------------------------------------------------------------------
    def _txt(self, texto, x, y, fonte=None, cor=C_TEXTO):
        fonte = fonte or self.f_med
        img = fonte.render(texto, True, cor)
        self.tela.blit(img, (x, y))
        return y + img.get_height() + 2

    def _quebrar(self, texto, fonte, larg):
        linhas, atual = [], ""
        for p in texto.split():
            teste = (atual + " " + p).strip()
            if fonte.size(teste)[0] <= larg:
                atual = teste
            else:
                linhas.append(atual)
                atual = p
        if atual:
            linhas.append(atual)
        return linhas

    def _desenhar_painel(self):
        pg, s, sim = self.pg, self.tela, self.sim
        pg.draw.rect(s, C_PAINEL, (PX - 10, 10, LARG_TELA - PX, ALT_TELA - 20), border_radius=10)
        y = self._txt("MICROMOUSE · X TUR", PX, 20, self.f_tit)
        y = self._txt("%s  ·  %.0f x %.0f cm" % (NOMES_FASE[sim.fase], sim.n * CELULA_CM, sim.n * CELULA_CM),
                      PX, y, self.f_peq, C_TEXTO_FRACO)
        y += 4
        y = self._txt("Tempo de acesso ao maze", PX, y, self.f_peq, C_TEXTO_FRACO)
        cor = C_ERRO if sim.tempo_restante < 60 else C_TEXTO
        y = self._txt(fmt_mmss(sim.tempo_restante), PX, y, self.f_gra, cor)

        c = sim.corrida
        if c:
            tipo = "Reconhecimento" if c["tipo"] == "reconhecimento" else "Corrida RÁPIDA"
            y = self._txt(tipo + ("  (pausado)" if sim.pausado else ""), PX, y + 2, self.f_med, C_OK)
            if c["tipo"] == "rapida":
                t = sim.tempo_corrida()
                y = self._txt("Cronômetro: %.3f s" % t if c["cron"] else "Cronômetro: aguardando partida",
                              PX, y, self.f_med)
            else:
                y = self._txt("Tempo não conta p/ classificação", PX, y, self.f_peq, C_TEXTO_FRACO)
        else:
            y = self._txt("Robô parado no início" if not sim.fim else "FIM DO TEMPO", PX, y + 2,
                          self.f_med, C_TEXTO_FRACO if not sim.fim else C_ERRO)
        y += 4
        melhor = "%.3f s" % sim.melhor if sim.melhor is not None else "—"
        media = "%.3f s" % sim.media if sim.media is not None else "—"
        y = self._txt("Tempo oficial: " + melhor, PX, y, self.f_med, C_OK if sim.melhor else C_TEXTO)
        y = self._txt("Rápidas válidas: %d   inválidas: %d" % (len(sim.tempos_validos), sim.rapidas_invalidas),
                      PX, y, self.f_peq)
        y = self._txt("Média das válidas: " + media, PX, y, self.f_peq)
        y = self._txt("Reconhecimentos: %d" % sim.n_recon, PX, y, self.f_peq)
        pen = sim.penalidades * PENALIDADE_REPOSICIONAMENTO_S
        y = self._txt("Penalidade pendente: +%d s" % pen, PX, y, self.f_peq, C_ERRO if pen else C_TEXTO)
        y = self._txt("Destino: " + ("já encontrado" if sim.destino_visto else "ainda não encontrado"),
                      PX, y, self.f_peq, C_OK if sim.destino_visto else C_TEXTO)
        y = self._txt("Velocidade: %dx" % VELOCIDADES[self.vel_idx], PX, y, self.f_peq, C_TEXTO_FRACO)
        # log
        y += 4
        pg.draw.line(s, C_BOTAO, (PX, y), (PX + 280, y))
        y += 6
        linhas = []
        for msg in sim.log[-6:]:
            linhas += self._quebrar("• " + msg, self.f_peq, 280)
        limite = self.botoes[0][1].top - 8
        for ln in linhas[-((limite - y) // 17):]:
            self._txt(ln, PX, y, self.f_peq, C_TEXTO_FRACO)
            y += 17
        # botoes
        pos = pg.mouse.get_pos()
        for bid, r in self.botoes:
            on = self._habilitado(bid)
            cor = C_BOTAO if on else C_BOTAO_OFF
            if on and r.collidepoint(pos):
                cor = (90, 98, 120)
            pg.draw.rect(s, cor, r, border_radius=7)
            rot = self.rotulos[bid]
            if bid == "pausa" and sim.pausado:
                rot = "Retomar (Espaço)"
            elif bid == "fase":
                rot = "Fase: %dx%d (T)" % (sim.n, sim.n)
            elif bid == "destino":
                rot = "Destino: %s (G)" % ("sim" if self.mostrar_destino else "não")
            elif bid == "explorado":
                rot = "Explorado: %s (V)" % ("sim" if self.mostrar_explorado else "não")
            img = self.f_peq.render(rot, True, C_TEXTO if on else C_TEXTO_FRACO)
            s.blit(img, img.get_rect(center=r.center))

    def desenhar(self):
        self.tela.fill(C_FUNDO)
        self._desenhar_maze()
        self._desenhar_painel()
        self.pg.display.flip()

    # -- loop --------------------------------------------------------------------
    def rodar(self):
        pg = self.pg
        relogio = pg.time.Clock()
        while True:
            dt = relogio.tick(60) / 1000.0
            for ev in pg.event.get():
                if ev.type == pg.QUIT or (ev.type == pg.KEYDOWN and ev.key == pg.K_ESCAPE):
                    pg.quit()
                    return
                if ev.type == pg.KEYDOWN:
                    ch = ev.unicode.lower() if ev.unicode else ""
                    if ev.key == pg.K_KP_PLUS:
                        ch = "+"
                    elif ev.key == pg.K_KP_MINUS:
                        ch = "-"
                    bid = self.TECLAS.get(ch)
                    if bid and self._habilitado(bid):
                        self.acao(bid)
                if ev.type == pg.MOUSEBUTTONDOWN and ev.button == 1:
                    for bid, r in self.botoes:
                        if r.collidepoint(ev.pos) and self._habilitado(bid):
                            self.acao(bid)
            self.sim.atualizar(min(dt, 0.1))
            self.desenhar()


# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Simulador de Micromouse (X TUR)")
    ap.add_argument("--movimento", default="movimento",
                    help="modulo Python do robo com setup() e passo() (padrão: movimento)")
    ap.add_argument("--fase", choices=list(TAMANHOS), default="classificatoria")
    ap.add_argument("--semente", type=int, default=None)
    ap.add_argument("--teste", type=int, nargs="?", const=5, default=None,
                    help="roda N mazes de cada fase sem janela e confere os tempos")
    ap.add_argument("--captura", default=None, help="(depuração) salva um PNG e sai")
    args = ap.parse_args()

    mov = importlib.import_module(args.movimento)

    if args.teste is not None:
        modo_teste(mov, args.teste, args.semente if args.semente is not None else 1)
        return

    sim = Simulacao(mov, args.fase, args.semente)
    if args.captura:
        import os
        os.environ.setdefault("SDL_VIDEODRIVER", "dummy")
        ui = Interface(sim)
        sim.iniciar_corrida("reconhecimento")
        sim.vel = 1
        sim.atualizar(60)
        ui.desenhar()
        ui.pg.image.save(ui.tela, args.captura)
        return
    Interface(sim).rodar()


if __name__ == "__main__":
    main()
