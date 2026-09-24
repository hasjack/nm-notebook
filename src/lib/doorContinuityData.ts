// Generated from analysis/deeper-door-continuity + gap-ingredients.
export const doorContinuityData = {
  "deeper": {
    "limit": 10000000,
    "disjoint": 623281,
    "deeperAny": 114709,
    "deeperPct": 18.4,
    "deeperNon5": 63588,
    "deeperNon5Pct": 10.2,
    "oldWithout5DeeperPct": 9.8,
    "baselines": [
      {
        "offset": 137,
        "deeperPct": 16.12
      },
      {
        "offset": 389,
        "deeperPct": 16.15
      },
      {
        "offset": 613,
        "deeperPct": 16.15
      }
    ],
    "example": {
      "p": 499,
      "next": 503,
      "oldDoor": "500 = 2\u00b2 \u00b7 5\u00b3",
      "newDoor": "502 = 2 \u00b7 251",
      "path": "503 \u2192 251 \u2192 5 while 499 \u2192 5"
    }
  },
  "gapArrival": {
    "limit": 10000000,
    "bins": [
      {
        "gapBin": "2\u20138",
        "pairs": 235079,
        "tenfoldPct": 30.42
      },
      {
        "gapBin": "10\u201318",
        "pairs": 186612,
        "tenfoldPct": 30.4
      },
      {
        "gapBin": "20\u201338",
        "pairs": 130671,
        "tenfoldPct": 30.23
      },
      {
        "gapBin": "40\u201378",
        "pairs": 32572,
        "tenfoldPct": 30.3
      },
      {
        "gapBin": "80+",
        "pairs": 1147,
        "tenfoldPct": 30.86
      }
    ],
    "partialCorr": 0.023
  }
} as const;
