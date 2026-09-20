import { useCallback, useMemo } from "react";
import { useSearchParams } from "react-router-dom";
import { WalkPage } from "./WalkPage";
import { LockIPage } from "./LockIPage";
import { LockPiPage } from "./LockPiPage";
import { BaselPage } from "./BaselPage";
import { FreePage } from "./FreePage";

export type AlphabetTab = "walk" | "lock-i" | "lock-pi" | "basel" | "free";

const TABS: { id: AlphabetTab; label: string }[] = [
  { id: "walk", label: "Walk" },
  { id: "lock-i", label: "Lock i" },
  { id: "lock-pi", label: "Lock π" },
  { id: "basel", label: "Basel" },
  { id: "free", label: "Free" },
];

const TAB_IDS = new Set<string>(TABS.map((t) => t.id));

function parseTab(raw: string | null): AlphabetTab {
  if (raw && TAB_IDS.has(raw)) return raw as AlphabetTab;
  return "walk";
}

/** Tabbed host for Walk / Lock i / Lock π / Basel / Free. Default tab: Walk. */
export function AlphabetPage() {
  const [params, setParams] = useSearchParams();
  const tab = useMemo(() => parseTab(params.get("tab")), [params]);

  const setTab = useCallback(
    (next: AlphabetTab) => {
      setParams(
        (prev) => {
          const p = new URLSearchParams(prev);
          if (next === "walk") p.delete("tab");
          else p.set("tab", next);
          return p;
        },
        { replace: true },
      );
    },
    [setParams],
  );

  return (
    <div className="alphabet-shell">
      <div className="alphabet-tabs" role="tablist" aria-label="Alphabet">
        {TABS.map((t) => (
          <button
            key={t.id}
            type="button"
            role="tab"
            aria-selected={tab === t.id}
            className={tab === t.id ? "alphabet-tab on" : "alphabet-tab"}
            onClick={() => setTab(t.id)}
          >
            {t.label}
          </button>
        ))}
      </div>
      <div className="alphabet-panel" role="tabpanel">
        {tab === "walk" && <WalkPage />}
        {tab === "lock-i" && <LockIPage />}
        {tab === "lock-pi" && <LockPiPage />}
        {tab === "basel" && <BaselPage />}
        {tab === "free" && <FreePage />}
      </div>
    </div>
  );
}
