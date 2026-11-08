# Conformance study: summary (7613 pairs)

## Corpus

| family | kind | pairs | model safe | model unsafe |
|---|---|---|---|---|
| aux | ext | 167 | 167 | 0 |
| aux | std | 120 | 120 | 0 |
| d1 | ext | 95 | 95 | 0 |
| d1 | std | 91 | 91 | 0 |
| d3 | ext | 167 | 167 | 0 |
| d3 | std | 120 | 120 | 0 |
| exact | ext | 167 | 167 | 0 |
| exact | std | 120 | 120 | 0 |
| kp | ext | 167 | 167 | 0 |
| kp | std | 120 | 120 | 0 |
| mmut | ext | 763 | 667 | 96 |
| mmut | std | 691 | 569 | 122 |
| mut | ext | 2289 | 2289 | 0 |
| mut | std | 2073 | 2073 | 0 |
| order | ext | 183 | 183 | 0 |
| order | std | 160 | 160 | 0 |
| ric3 | std | 120 | 120 | 0 |

Ground truth undecided: 0

## Scope of the reference checker

| verdict | pairs |
|---|---|
| accept | 4299 |
| reject | 2755 |
| refused | 559 |

Refusal reasons:

- witness: 343
- negated mapping: 125
- gate mapping: 91

## Verdicts (ground truth x reference checker x Certifaiger current x 10.2.1)

| model | reference | current | 10.2.1 | pairs |
|---|---|---|---|---|
| safe | reject | reject | reject | 2537 |
| safe | accept | accept | accept | 1840 |
| safe | accept | accept | reject | 1378 |
| safe | accept | reject | reject | 1081 |
| safe | refused | reject | reject | 275 |
| unsafe | reject | reject | reject | 218 |
| safe | refused | error | error | 158 |
| safe | refused | error | reject | 98 |
| safe | refused | accept | accept | 19 |
| safe | refused | accept | reject | 9 |

## Predictions

**P1** no checker accepts an unsafe model: HOLDS  (cf 0, co 0, ca 0, va 0)
**P2** the reference checker accepts no unsafe model: HOLDS (0)
**P3** in scope (7054 pairs), Certifaiger never accepts what the reference rejects: HOLDS (0)
**P4** reference accepts, Certifaiger rejects: 1081 pairs; D1 306, D2 0, D3 775, unexplained 0: HOLDS
**P5** current accepts, 10.2.1 rejects: 1387 pairs; all 'not stratified' and accepted by the reference: FALSIFIED (9): m0008_kp_mut0 m0119_d1_mut2 m0180_kp_mut1 m0215_exact_mut0 m0343_kp_mut1 m0385_kp_mut0 m0408_kp_mut0 m0408_kp_mut2 m0558_kp_mut0
  - by family: mut 692, kp 280, mmut 275, exact 76, aux 58, d1 6
**P6** ground truth agrees with rIC3 on 120 std models both decide: HOLDS (0 disagreements)

## Valaig

Outcomes (from its messages): out of scope 6621, accept 633, reject 359
By model kind: ext/accept 175, ext/out of scope 3727, ext/reject 96, std/accept 458, std/out of scope 2894, std/reject 263
Valaig accepts 633 pairs: Certifaiger current {'accept': 468, 'reject': 165}, reference {'accept': 468, 'reject': 155, 'refused': 10}
Certifaiger accepts and Valaig does not, std models: 1278

## Robustness

- Certifaiger current, release: order/error 256
- Certifaiger current, assertions on: order/crash 256
- Certifaiger 10.2.1: order/error 158
- current, release, exit codes on errors: order rc=1 256

## Cost

Reference checker (front end + kcheck), in scope: median 0.082 s, 90th 0.110 s, max 5.604 s
Certifaiger current: median 0.175 s, 90th 0.217 s, max 5.709 s

Predictions: P1 holds, P2 holds, P3 holds, P4 holds, P5 FALSIFIED, P6 holds
