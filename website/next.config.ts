import type { NextConfig } from "next";

const siteUrl = process.env.NEXT_PUBLIC_SITE_URL?.replace(/\/$/, "") ?? "";
const basePath = process.env.NEXT_PUBLIC_BASE_PATH?.replace(/\/$/, "") ?? "";

const nextConfig: NextConfig = {
  // GitHub Pages is a static host. Vinext prerenders the one-page application
  // into dist/client. The real base path keeps client routing inside the
  // project site, while an absolute prefix makes framework assets canonical.
  output: "export",
  basePath,
  assetPrefix: siteUrl || undefined,
  trailingSlash: true,
  // Vinext 1.0.0-beta.2 probes `/` rather than applying basePath during static
  // prerendering. This no-op exemption admits only that build-time root probe;
  // the exported client and router still retain the real Pages base path.
  async rewrites() {
    return basePath ? [{ source: "/", destination: "/", basePath: false }] : [];
  },
};

export default nextConfig;
