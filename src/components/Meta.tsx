import { useEffect } from "react";
import { useLocation } from "react-router-dom";
import {
  SITE_IMAGE,
  SITE_NAME,
  metaFor,
} from "../lib/meta";

function upsertMeta(selector: string, attrs: Record<string, string>) {
  let el = document.head.querySelector(selector) as HTMLMetaElement | HTMLLinkElement | null;
  if (!el) {
    const tag = selector.startsWith("link") ? "link" : "meta";
    el = document.createElement(tag);
    document.head.appendChild(el);
  }
  for (const [k, v] of Object.entries(attrs)) el.setAttribute(k, v);
}

export function Meta() {
  const { pathname } = useLocation();
  useEffect(() => {
    const { title, description, url } = metaFor(pathname);
    document.title = title;
    upsertMeta('meta[name="description"]', { name: "description", content: description });
    upsertMeta('link[rel="canonical"]', { rel: "canonical", href: url });
    upsertMeta('meta[property="og:title"]', { property: "og:title", content: title });
    upsertMeta('meta[property="og:description"]', {
      property: "og:description",
      content: description,
    });
    upsertMeta('meta[property="og:url"]', { property: "og:url", content: url });
    upsertMeta('meta[property="og:image"]', { property: "og:image", content: SITE_IMAGE });
    upsertMeta('meta[property="og:site_name"]', {
      property: "og:site_name",
      content: SITE_NAME,
    });
    upsertMeta('meta[name="twitter:title"]', { name: "twitter:title", content: title });
    upsertMeta('meta[name="twitter:description"]', {
      name: "twitter:description",
      content: description,
    });
  }, [pathname]);
  return null;
}
