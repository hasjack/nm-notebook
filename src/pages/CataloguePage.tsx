import { useMemo, useState } from "react";
import {
  CATALOGUE,
  GRADE_BLURB,
  GRADE_LABEL,
  type Grade,
} from "../lib/catalogue";

const FILTERS: Array<Grade | "all"> = ["all", "clean", "calligraphy", "refuses"];

export function CataloguePage() {
  const [filter, setFilter] = useState<Grade | "all">("all");

  const entries = useMemo(
    () =>
      filter === "all"
        ? CATALOGUE
        : CATALOGUE.filter((e) => e.grade === filter),
    [filter]
  );

  const counts = useMemo(() => {
    const c = { clean: 0, calligraphy: 0, refuses: 0 };
    for (const e of CATALOGUE) c[e.grade]++;
    return c;
  }, []);

  return (
    <main className="page catalogue">
      <h1>Catalogue — clean rewrites</h1>
      <p className="lede">
        A hunting list for a thought-provoking video: classical facts rewritten
        in the alphabet <strong>{"{e, i, π}"}</strong>.{" "}
        <em>Clean</em> means the letters earn their keep.{" "}
        <em>Calligraphy</em> means we renamed π (usually via Log(−1)).{" "}
        <em>Refuses</em> means the island has no tidy answer yet — ζ(3) lives
        here.
      </p>

      <div className="modes" style={{ marginBottom: "1rem" }}>
        {FILTERS.map((f) => (
          <button
            key={f}
            type="button"
            className={filter === f ? "on" : ""}
            onClick={() => setFilter(f)}
            style={{
              background: filter === f ? "#1f4e79" : "#fffaf3",
              color: filter === f ? "#fff" : "#1a1a1a",
              border: "1px solid #e2d8c8",
              borderRadius: 8,
              padding: "0.4rem 0.85rem",
              font: "inherit",
              cursor: "pointer",
            }}
          >
            {f === "all"
              ? `All (${CATALOGUE.length})`
              : `${GRADE_LABEL[f]} (${counts[f]})`}
          </button>
        ))}
      </div>

      <p className="hint">{filter === "all" ? GRADE_BLURB.clean : GRADE_BLURB[filter]}</p>

      <div className="catalogue-list">
        {entries.map((e) => (
          <article key={e.id} className={`catalogue-card grade-${e.grade}`}>
            <header className="catalogue-card-head">
              <h2>{e.title}</h2>
              <span className={`grade-pill grade-${e.grade}`}>
                {GRADE_LABEL[e.grade]}
              </span>
            </header>
            <div className="catalogue-forms">
              <div>
                <div className="kv-label">Classical</div>
                <div className="catalogue-formula">{e.classical}</div>
              </div>
              <div>
                <div className="kv-label">Rewrite</div>
                <div className="catalogue-formula">{e.rewrite}</div>
              </div>
            </div>
            <p className="catalogue-alphabet">
              Alphabet:{" "}
              {e.alphabet.length === 0
                ? "— (none tidy)"
                : e.alphabet.map((a) => a).join(", ")}
            </p>
            <p>{e.why}</p>
            <p className="catalogue-beat">
              <strong>Video beat:</strong> {e.videoBeat}
            </p>
          </article>
        ))}
      </div>

      <section style={{ marginTop: "2rem" }}>
        <h2>Suggested video arc</h2>
        <ol className="benefits">
          <li>Open on Euler’s identity — the alphabet in one line.</li>
          <li>Show Walk: don’t treat e as constant; base moves, iπ fixed.</li>
          <li>Clean hits: i^i, ζ(2), Gaussian, 2πi — letters earning rent.</li>
          <li>
            Calligraphy twist: circle area as −i Log(−1) r² — same pizza, new
            font.
          </li>
          <li>
            Shoreline: ζ(3) refuses. Odd vs even as landscape, not lottery.
          </li>
          <li>Close on Lock i / Lock π: freeze one letter, watch the other move.</li>
        </ol>
      </section>
    </main>
  );
}
