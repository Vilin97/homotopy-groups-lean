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
    "An interactive (n,k)-lattice of known, partial, disputed, and Lean 4-formalized homotopy groups of spheres.",
  alternates: { canonical: canonicalUrl },
  openGraph: {
    title: "πₙ₊ₖ(Sⁿ), mapped.",
    description: "Explore the homotopy knowledge lattice, then formalize its gaps in Lean.",
    url: canonicalUrl,
    siteName: "Homotopy Groups Lean",
    type: "website",
    images: [{ url: socialImageUrl, width: 1200, height: 630 }],
  },
  twitter: {
    card: "summary_large_image",
    title: "πₙ₊ₖ(Sⁿ), mapped.",
    description: "The interactive homotopy knowledge lattice.",
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
