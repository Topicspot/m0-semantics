# M₀: semántica determinista de estado

[English](../README.md) · [Русский](README.ru.md) · [简体中文](README.zh-CN.md) · **Español** · [Português](README.pt-BR.md)

M₀ es un modelo formal pequeño de *estado que forma parte del protocolo mientras que el
plan de ejecución no*. Apunta a sistemas donde reproducir una ejecución debe producir una
salida observable idéntica byte a byte: máquinas de estado replicadas, simulaciones
deterministas, motores de emparejamiento, núcleos de bases de datos.

La propiedad estudiada, informalmente:

> si dos planes de ejecución son semánticamente equivalentes para el mismo diario, la salida
> observable de la ejecución es idéntica

Formalmente `schedule₁ ≈_J schedule₂ ⇒ Observable(run₁) = Observable(run₂)`, con la
referencia `Seq(P, J) = fold(J)`.

El modelo: celdas transaccionales, ejecución optimista sobre un snapshot, validación del
snapshot al hacer commit, commit estrictamente en el orden del diario.

## Resultados demostrados

| Capa | Contenido | Estado |
| --- | --- | --- |
| L1 | fold secuencial determinista | demostrado |
| L2 | commit ordenado + validación ⇒ Parallel = Seq | demostrado |
| L3A / L3B | frontera de extensiones admisibles + contraejemplo `scheduleCounter` | demostrado |
| L3.5 | semantic ⊊ observable ⊊ coincidence | demostrado |
| L4 | independencia del sustrato (`SoundSubstrate`) | demostrado |
| L5 | tolerancia a fallos: la ley `forced` debilitada a un *prefijo* del diario (`FailSoundSubstrate`), máquina crash-stop como instancia | demostrado, publicado en v1.1 |

Mecanización: Lean 4.31.0, `0 sorry`, los únicos axiomas son `propext` y `Quot.sound`; el
teorema principal, `substrate_independence`, no usa ninguno. Además hay un testigo
diferencial hostil, `witness/m0.py`, con sustratos negativos y una puerta de cobertura.

## Inicio rápido

Lean 4.31.0 (instalado automáticamente por `elan` desde `lean-toolchain`) y Python 3.10+.

```bash
lake build                 # compila los seis archivos Lean
python scripts/verify.py   # build + 0 sorry + huella de axiomas + testigo
```

`scripts/verify.py` es el mismo comando que ejecuta CI: imprime `PASS` solo si la
compilación está limpia, ningún archivo contiene `sorry`, la huella de axiomas de cada
teorema coincide con la documentada y el testigo reporta `ALL CHECKS PASSED`.

## Límites

La semántica de costes, la liveness y una implementación industrial quedan fuera del
artefacto: M₀ es una historia de safety. El testigo es una herramienta de falsación, no una
segunda demostración.

La documentación completa, la estructura del repositorio y los detalles del testigo están en
el [README en inglés](../README.md).

## Licencia

Doble licencia: Apache-2.0 y MIT.
