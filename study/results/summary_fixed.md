# Conformance study: summary (16 pairs)

## Corpus

| family | kind | pairs | model safe | model unsafe |
|---|---|---|---|---|
| certifaiger-tests | - | 14 | 12 | 1 |
| handmade | - | 2 | 2 | 0 |

Ground truth undecided: 1

## Scope of the reference checker

| verdict | pairs |
|---|---|
| refused | 8 |
| accept | 7 |
| reject | 1 |

Refusal reasons:

- liveness: 5
- input-latch mapping: 1
- gate mapping: 1
- enumeration budget exceeded: 1

## Verdicts (ground truth x reference checker x Certifaiger current x 10.2.1)

| model | reference | current | 10.2.1 | pairs |
|---|---|---|---|---|
| safe | refused | accept | accept | 6 |
| safe | accept | accept | accept | 5 |
| safe | refused | reject | accept | 1 |
| unsafe | reject | reject | reject | 1 |
| error | refused | accept | accept | 1 |
| safe | accept | accept | reject | 1 |
| safe | accept | reject | reject | 1 |

## Predictions

**P1** no checker accepts an unsafe model: HOLDS  (cf 0, co 0, ca 0, va 0)
**P2** the reference checker accepts no unsafe model: HOLDS (0)
**P3** in scope (8 pairs), Certifaiger never accepts what the reference rejects: HOLDS (0)
**P4** reference accepts, Certifaiger rejects: 1 pairs; D1 1, D2 0, D3 0, unexplained 0: HOLDS
**P5** current accepts, 10.2.1 rejects: 1 pairs; all 'not stratified' and accepted by the reference: HOLDS
  - by family: handmade 1

## Valaig

Outcomes (from its messages): out of scope 14, reject 1, accept 1
By model kind: -/accept 1, -/out of scope 14, -/reject 1
Valaig accepts 1 pairs: Certifaiger current {'accept': 1}, reference {'accept': 1}
Certifaiger accepts and Valaig does not, std models: 0

## Robustness

- Certifaiger current, release: none
- Certifaiger current, assertions on: none
- Certifaiger 10.2.1: none
- current, release, exit codes on errors: 

## Cost

Reference checker (front end + kcheck), in scope: median 0.166 s, 90th 0.179 s, max 0.191 s
Certifaiger current: median 0.349 s, 90th 0.389 s, max 1.677 s

Predictions: P1 holds, P2 holds, P3 holds, P4 holds, P5 holds
