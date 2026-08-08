import type { Metadata } from "next";
import "./globals.css";
import { PRODUCTION_SITE_URL } from "./site";

const canonicalUrl = `${PRODUCTION_SITE_URL}/`;
const socialImageUrl = `${PRODUCTION_SITE_URL}/og.png`;
const faviconUrl = `${PRODUCTION_SITE_URL}/favicon.svg`;

export const metadata: Metadata = {
  metadataBase: new URL(canonicalUrl),
  title: {
    default: "Homotopy Groups Lean",
    template: "%s · Homotopy Groups Lean",
  },
  description:
    "An open, comparator-gated Lean benchmark for known results and open problems in homotopy groups.",
  alternates: { canonical: canonicalUrl },
  openGraph: {
    title: "The known edge of homotopy, formalized.",
    description: "A versioned Lean benchmark for homotopy groups, stable stems, and open conjectures.",
    url: canonicalUrl,
    siteName: "Homotopy Groups Lean",
    type: "website",
    images: [{ url: socialImageUrl, width: 1200, height: 630 }],
  },
  twitter: {
    card: "summary_large_image",
    title: "Homotopy Groups Lean",
    description: "The known edge of homotopy, formalized.",
    images: [socialImageUrl],
  },
  icons: {
    icon: faviconUrl,
    shortcut: faviconUrl,
  },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
