# e-walk-app

Jack’s local explorer for a number line spoken only in **e**, **i**, and **π**.

Identity held fixed:

> base^(k · i · π) = −1  ⇔  k · ln(base) = odd integer

## Run

```bash
npm install
npm run dev
```

Then open the URL Vite prints (usually http://localhost:5173/).

## Routes

| Path | View |
|------|------|
| `/` | **Walk** — free k, favourite Plotly 3D ribbon at base e |
| `/lock` | **Lock −1** — base in ln-space, odd branch, 3D + 2D locus |
| `/split` | **Split i & π** — base^(α·i·βπ), share dial trades α vs β |
| `/notes` | **Benefits & notes** — prose on the e/i/π line |

## Maths

Ported from the reference `walk.ts` into `src/lib/walk.ts`.

## Build

```bash
npm run build
```
