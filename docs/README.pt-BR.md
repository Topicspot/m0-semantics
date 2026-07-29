# M₀: semântica determinística de estado

[English](../README.md) · [Русский](README.ru.md) · [简体中文](README.zh-CN.md) · [Español](README.es.md) · **Português**

M₀ é um modelo formal pequeno de *estado que faz parte do protocolo enquanto o escalonamento
não faz*. Ele mira sistemas em que reproduzir uma execução deve gerar saída observável
idêntica byte a byte: máquinas de estado replicadas, simulações determinísticas, motores de
matching, núcleos de bancos de dados.

A propriedade estudada, informalmente:

> se dois escalonamentos são semanticamente equivalentes para o mesmo diário, a saída
> observável da execução é idêntica

Formalmente `schedule₁ ≈_J schedule₂ ⇒ Observable(run₁) = Observable(run₂)`, com a
referência `Seq(P, J) = fold(J)`.

O modelo: células transacionais, execução otimista sobre um snapshot, validação do snapshot
no commit, commit estritamente na ordem do diário.

## Resultados provados

| Camada | Conteúdo | Estado |
| --- | --- | --- |
| L1 | fold sequencial determinístico | provado |
| L2 | commit ordenado + validação ⇒ Parallel = Seq | provado |
| L3A / L3B | fronteira das extensões admissíveis + contraexemplo `scheduleCounter` | provado |
| L3.5 | semantic ⊊ observable ⊊ coincidence | provado |
| L4 | independência de substrato (`SoundSubstrate`) | provado |
| L5 | tolerância a falhas: a lei `forced` enfraquecida para um *prefixo* do diário (`FailSoundSubstrate`), máquina crash-stop como instância | provado, publicado na v1.1 |

Mecanização: Lean 4.31.0, `0 sorry`, os únicos axiomas são `propext` e `Quot.sound`; o
teorema principal, `substrate_independence`, não usa nenhum. Há ainda uma testemunha
diferencial hostil, `witness/m0.py`, com substratos negativos e um portão de cobertura.

## Início rápido

Lean 4.31.0 (instalado automaticamente pelo `elan` a partir de `lean-toolchain`) e
Python 3.10+.

```bash
lake build                 # compila os seis arquivos Lean
python scripts/verify.py   # build + 0 sorry + pegada de axiomas + testemunha
```

`scripts/verify.py` é o mesmo comando que o CI executa: imprime `PASS` somente se a
compilação estiver limpa, nenhum arquivo contiver `sorry`, a pegada de axiomas de cada
teorema bater com a documentada e a testemunha reportar `ALL CHECKS PASSED`.

## Limites

Semântica de custo, liveness e uma implementação industrial ficam fora do artefato: M₀ é uma
história de safety. A testemunha é uma ferramenta de falseamento, não uma segunda prova.

A documentação completa, a estrutura do repositório e os detalhes da testemunha estão no
[README em inglês](../README.md).

## Licença

Licença dupla: Apache-2.0 e MIT.
