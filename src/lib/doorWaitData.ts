// Generated from analysis/door-coverage/waits-results.json.
export const doorWaitData = {
  "limit": 10000000,
  "smallFactorBound": 100,
  "ingredients": [
    5,
    7,
    49,
    11
  ],
  "overall": [
    {
      "q": 5,
      "candidates": 666666,
      "primeHits": 166111,
      "meanMisses": 3.013,
      "p90Misses": 7,
      "maxMisses": 41,
      "meanMissesAfterSieve": 0.811,
      "composites": 500555,
      "blockedByLeq100": 365793,
      "shareRemoved": 73.08,
      "topBlockers": [
        [
          "7",
          95238
        ],
        [
          "11",
          51947
        ],
        [
          "13",
          39960
        ],
        [
          "17",
          28207
        ],
        [
          "19",
          23752
        ]
      ],
      "switch": 97860,
      "same": 68250,
      "switchShare": 58.91,
      "equalHazardBaseline": 57.12,
      "longest": {
        "start": 3542141,
        "end": 3542771,
        "misses": 41,
        "survivingMisses": 13,
        "numericGap": 630
      },
      "firstHire": 11,
      "leadingMisses": 0,
      "sieveAwareSwitchShare": 58.75,
      "rawIndependentSwitchShare": 57.12
    },
    {
      "q": 7,
      "candidates": 476190,
      "primeHits": 110749,
      "meanMisses": 3.3,
      "p90Misses": 8,
      "maxMisses": 41,
      "meanMissesAfterSieve": 0.811,
      "composites": 365441,
      "blockedByLeq100": 275618,
      "shareRemoved": 75.42,
      "topBlockers": [
        [
          "5",
          95238
        ],
        [
          "11",
          34632
        ],
        [
          "13",
          26639
        ],
        [
          "17",
          18805
        ],
        [
          "19",
          15835
        ]
      ],
      "switch": 64458,
      "same": 46290,
      "switchShare": 58.2,
      "equalHazardBaseline": 56.58,
      "longest": {
        "start": 4456339,
        "end": 4457221,
        "misses": 41,
        "survivingMisses": 10,
        "numericGap": 882
      },
      "firstHire": 13,
      "leadingMisses": 0,
      "sieveAwareSwitchShare": 58.32,
      "rawIndependentSwitchShare": 56.58
    },
    {
      "q": 49,
      "candidates": 68027,
      "primeHits": 15771,
      "meanMisses": 3.313,
      "p90Misses": 8,
      "maxMisses": 33,
      "meanMissesAfterSieve": 0.816,
      "composites": 52256,
      "blockedByLeq100": 39384,
      "shareRemoved": 75.37,
      "topBlockers": [
        [
          "5",
          13606
        ],
        [
          "11",
          4947
        ],
        [
          "13",
          3806
        ],
        [
          "17",
          2686
        ],
        [
          "19",
          2263
        ]
      ],
      "switch": 9292,
      "same": 6478,
      "switchShare": 58.92,
      "equalHazardBaseline": 56.56,
      "longest": {
        "start": 5731433,
        "end": 5736431,
        "misses": 33,
        "survivingMisses": 9,
        "numericGap": 4998
      },
      "firstHire": 97,
      "leadingMisses": 0,
      "sieveAwareSwitchShare": 58.8,
      "rawIndependentSwitchShare": 56.56
    },
    {
      "q": 11,
      "candidates": 303030,
      "primeHits": 66487,
      "meanMisses": 3.558,
      "p90Misses": 9,
      "maxMisses": 37,
      "meanMissesAfterSieve": 0.81,
      "composites": 236543,
      "blockedByLeq100": 182672,
      "shareRemoved": 77.23,
      "topBlockers": [
        [
          "5",
          60606
        ],
        [
          "7",
          34632
        ],
        [
          "13",
          15984
        ],
        [
          "17",
          11283
        ],
        [
          "19",
          9502
        ]
      ],
      "switch": 39071,
      "same": 27415,
      "switchShare": 58.77,
      "equalHazardBaseline": 56.16,
      "longest": {
        "start": 1583053,
        "end": 1584307,
        "misses": 37,
        "survivingMisses": 8,
        "numericGap": 1254
      },
      "firstHire": 23,
      "leadingMisses": 0,
      "sieveAwareSwitchShare": 59.09,
      "rawIndependentSwitchShare": 56.16
    }
  ],
  "bands": [
    {
      "q": 5,
      "lowerExclusive": 0,
      "upperInclusive": 10000,
      "meanMisses": 1.188,
      "meanMissesAfterSieve": 0.0,
      "immediateNextSurvivorPrime": 100.0,
      "fittedIndependentBaseline": 100.0
    },
    {
      "q": 5,
      "lowerExclusive": 10000,
      "upperInclusive": 100000,
      "meanMisses": 1.876,
      "meanMissesAfterSieve": 0.272,
      "immediateNextSurvivorPrime": 78.6,
      "fittedIndependentBaseline": 78.6
    },
    {
      "q": 5,
      "lowerExclusive": 100000,
      "upperInclusive": 1000000,
      "meanMisses": 2.487,
      "meanMissesAfterSieve": 0.583,
      "immediateNextSurvivorPrime": 63.18,
      "fittedIndependentBaseline": 63.18
    },
    {
      "q": 5,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.095,
      "meanMissesAfterSieve": 0.847,
      "immediateNextSurvivorPrime": 54.13,
      "fittedIndependentBaseline": 54.13
    },
    {
      "q": 7,
      "lowerExclusive": 0,
      "upperInclusive": 10000,
      "meanMisses": 1.312,
      "meanMissesAfterSieve": 0.0,
      "immediateNextSurvivorPrime": 100.0,
      "fittedIndependentBaseline": 100.0
    },
    {
      "q": 7,
      "lowerExclusive": 10000,
      "upperInclusive": 100000,
      "meanMisses": 2.065,
      "meanMissesAfterSieve": 0.265,
      "immediateNextSurvivorPrime": 79.04,
      "fittedIndependentBaseline": 79.04
    },
    {
      "q": 7,
      "lowerExclusive": 100000,
      "upperInclusive": 1000000,
      "meanMisses": 2.733,
      "meanMissesAfterSieve": 0.58,
      "immediateNextSurvivorPrime": 63.28,
      "fittedIndependentBaseline": 63.28
    },
    {
      "q": 7,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.388,
      "meanMissesAfterSieve": 0.848,
      "immediateNextSurvivorPrime": 54.12,
      "fittedIndependentBaseline": 54.12
    },
    {
      "q": 49,
      "lowerExclusive": 0,
      "upperInclusive": 10000,
      "meanMisses": 1.333,
      "meanMissesAfterSieve": 0.0,
      "immediateNextSurvivorPrime": 100.0,
      "fittedIndependentBaseline": 100.0
    },
    {
      "q": 49,
      "lowerExclusive": 10000,
      "upperInclusive": 100000,
      "meanMisses": 2.102,
      "meanMissesAfterSieve": 0.286,
      "immediateNextSurvivorPrime": 77.87,
      "fittedIndependentBaseline": 77.87
    },
    {
      "q": 49,
      "lowerExclusive": 100000,
      "upperInclusive": 1000000,
      "meanMisses": 2.756,
      "meanMissesAfterSieve": 0.589,
      "immediateNextSurvivorPrime": 62.82,
      "fittedIndependentBaseline": 62.82
    },
    {
      "q": 49,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.398,
      "meanMissesAfterSieve": 0.851,
      "immediateNextSurvivorPrime": 54.01,
      "fittedIndependentBaseline": 54.01
    },
    {
      "q": 11,
      "lowerExclusive": 0,
      "upperInclusive": 10000,
      "meanMisses": 1.4,
      "meanMissesAfterSieve": 0.0,
      "immediateNextSurvivorPrime": 100.0,
      "fittedIndependentBaseline": 100.0
    },
    {
      "q": 11,
      "lowerExclusive": 10000,
      "upperInclusive": 100000,
      "meanMisses": 2.239,
      "meanMissesAfterSieve": 0.262,
      "immediateNextSurvivorPrime": 79.28,
      "fittedIndependentBaseline": 79.28
    },
    {
      "q": 11,
      "lowerExclusive": 100000,
      "upperInclusive": 1000000,
      "meanMisses": 2.955,
      "meanMissesAfterSieve": 0.58,
      "immediateNextSurvivorPrime": 63.24,
      "fittedIndependentBaseline": 63.24
    },
    {
      "q": 11,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.652,
      "meanMissesAfterSieve": 0.847,
      "immediateNextSurvivorPrime": 54.15,
      "fittedIndependentBaseline": 54.15
    }
  ],
  "switchBandMillion": [
    {
      "q": 5,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.095,
      "meanMissesAfterSieve": 0.847,
      "observedSwitchShare": 58.7,
      "rawIndependent": 56.95,
      "sieveAware": 58.58,
      "survivorSuccessRate": 54.13
    },
    {
      "q": 7,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.388,
      "meanMissesAfterSieve": 0.848,
      "observedSwitchShare": 58.05,
      "rawIndependent": 56.43,
      "sieveAware": 58.18,
      "survivorSuccessRate": 54.12
    },
    {
      "q": 49,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.398,
      "meanMissesAfterSieve": 0.851,
      "observedSwitchShare": 58.92,
      "rawIndependent": 56.41,
      "sieveAware": 58.63,
      "survivorSuccessRate": 54.01
    },
    {
      "q": 11,
      "lowerExclusive": 1000000,
      "upperInclusive": 10000000,
      "meanMisses": 3.652,
      "meanMissesAfterSieve": 0.847,
      "observedSwitchShare": 58.46,
      "rawIndependent": 56.02,
      "sieveAware": 58.91,
      "survivorSuccessRate": 54.15
    }
  ]
} as const;
