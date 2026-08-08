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
    "An open, comparator-gated Lean benchmark for known results and open problems in homotopy groups.",
  openGraph: {
    title: "The known edge of homotopy, formalized.",
    description: "A versioned Lean benchmark for homotopy groups, stable stems, and open conjectures.",
    images: [{ url: "/og.png", width: 1200, height: 630 }],
  },
  twitter: {
    card: "summary_large_image",
    title: "Homotopy Groups Lean",
    description: "The known edge of homotopy, formalized.",
    images: ["/og.png"],
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
