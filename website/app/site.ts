export const PRODUCTION_SITE_URL =
  "https://vilin97.github.io/homotopy-groups-lean";

const configuredBasePath = process.env.NEXT_PUBLIC_BASE_PATH ?? "";

export const SITE_BASE_PATH = configuredBasePath.replace(/\/+$/, "");

export function siteAsset(path: string): string {
  const absolutePath = path.startsWith("/") ? path : `/${path}`;
  return `${SITE_BASE_PATH}${absolutePath}`;
}
