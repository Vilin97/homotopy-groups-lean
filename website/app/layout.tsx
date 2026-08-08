import type { Metadata } from "next";
import { Geist, Geist_Mono } from "next/font/google";
import "./globals.css";

const geistSans = Geist({
  variable: "--font-geist-sans",
  subsets: ["latin"],
});

const geistMono = Geist_Mono({
  variable: "--font-geist-mono",
  subsets: ["latin"],
});

export const metadata: Metadata = {
  metadataBase: new URL("https://homotopy-groups-lean.lean4lean4.chatgpt.site"),
  title: {
    default: "Homotopy Groups Lean",
    template: "%s · Homotopy Groups Lean",
  },
  description:
    "An interactive (n,k)-lattice of known, partial, uncharted, and Lean-verified homotopy groups of spheres.",
  openGraph: {
    title: "πₙ₊ₖ(Sⁿ), mapped.",
    description: "Explore the homotopy knowledge lattice, then formalize its gaps in Lean.",
    images: [{ url: "/og-lattice.png", width: 1200, height: 630 }],
  },
  twitter: {
    card: "summary_large_image",
    title: "πₙ₊ₖ(Sⁿ), mapped.",
    description: "The interactive homotopy knowledge lattice.",
    images: ["/og-lattice.png"],
  },
  icons: {
    icon: "/favicon.svg",
    shortcut: "/favicon.svg",
  },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body className={`${geistSans.variable} ${geistMono.variable}`}>
        {children}
      </body>
    </html>
  );
}
