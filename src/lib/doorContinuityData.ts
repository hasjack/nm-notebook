// Generated from deeper-door-continuity + gap-ingredients + matched-door-continuity.
export const doorContinuityData = {
  "deeper": {
    "limit": 10000000,
    "disjoint": 623281,
    "deeperAny": 114709,
    "deeperPct": 18.4,
    "deeperNon5Pct": 10.2,
    "oldWithout5DeeperPct": 9.8,
    "example": {
      "p": 499,
      "next": 503,
      "oldDoor": "500 = 2\u00b2 \u00b7 5\u00b3",
      "newDoor": "502 = 2 \u00b7 251",
      "path": "503 \u2192 251 \u2192 5 while 499 \u2192 5",
      "note": "Gap 2 \u2014 outside the matched nonconsecutive control (gaps 2 and 4 have no intervening-prime controls)."
    }
  },
  "matched": {
    "rows": [
      {
        "minControls": 1,
        "matched": 501484,
        "coveragePct": 80.46,
        "observedPct": 16.17,
        "controlPct": 16.166,
        "diffPp": 0.004
      },
      {
        "minControls": 10,
        "matched": 463609,
        "coveragePct": 74.38,
        "observedPct": 15.31,
        "controlPct": 15.307,
        "diffPp": 0.003
      },
      {
        "minControls": 30,
        "matched": 394651,
        "coveragePct": 63.32,
        "observedPct": 14.17,
        "controlPct": 14.09,
        "diffPp": 0.08
      }
    ],
    "note": "Full match: exact gap + location band + both ingredient profiles. Gaps 2 and 4 cannot have nonconsecutive controls."
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
