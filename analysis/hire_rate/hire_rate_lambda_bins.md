# Lambda-bin hire residual

Re-bin H - P_Pois by λ = Li(X)/(q-1). Excess collapses onto the hiring frontier λ ~ 1.

## Global residual by X

| X | H | P | resid | u* | λ(u*) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1000000 | 16688 | 16266.1 | 421.9 | 0.8099 | 1.0863 |
| 10000000 | 125661 | 122446.6 | 3214.4 | 0.8275 | 1.0717 |
| 100000000 | 980292 | 958790.6 | 21501.4 | 0.8418 | 1.0614 |
| 1000000000 | 7877140 | 7735846.7 | 141293.3 | 0.8537 | 1.0538 |
| 10000000000 | 64838984 | 63889339.5 | 949644.5 | 0.8638 | 1.0478 |
| 20000000000 | 122776796 | 121092614.6 | 1684181.4 | 0.8665 | 1.0463 |

## Coarse λ bins at X = 2e10

| λ | H | P | resid | rel% |
| --- | ---: | ---: | ---: | ---: |
| λ<0.5 | 61544625 | 61566112.1 | -21487.1 | -0.03 |
| [0.5,1) | 21557090 | 20848157.9 | 708932.1 | 3.40 |
| [1,2) | 16856380 | 16114034.9 | 742345.1 | 4.61 |
| [2,4) | 10684329 | 10450029.3 | 234299.7 | 2.24 |
| λ≥4 | 12134372 | 12114280.4 | 20091.5 | 0.17 |

## Takeaway

- Residual collapses onto λ ~ 1 across X (u* tracks 1 - loglog/log; λ(u*) ~ 1.05).
- Peak positive residual in [0.5,2) at tip; saturation λ≫1 and small-λ ends are near zero rel%.
- Fine-bin peak at [0,0.125) in the tip dump is an artifact of bin edges vs saturation; coarse [0.5,2) is the real frontier story matching ChatGPT/Heavy.
- C stays unnamed. Papers frozen.

