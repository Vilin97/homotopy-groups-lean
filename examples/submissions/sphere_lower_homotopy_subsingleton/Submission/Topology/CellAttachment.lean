/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.WhiteheadTheorem.Shapes.Disk
import Submission.Topology.PushoutMono
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Attaching one topological cell

Given an attaching map `a : diskBoundary n ⟶ X`, this file defines the space obtained by attaching one
`n`-disk to `X` as the pushout of `a` and the boundary inclusion.  It records the two structure
maps, their universal property, and the elementary fact that an extension of `a` across the disk
gives a retraction onto `X`.

## Main definitions

* `Submission.cellAttachment a` is `X ∪ₐ Dⁿ`.
* `Submission.cellAttachmentIncl a` includes `X` into the attachment.
* `Submission.cellAttachmentDisk a` is the characteristic map of the attached disk.
* `Submission.cellAttachmentDesc` is the pushout eliminator.
* `Submission.cellAttachmentRetractOfExtension` constructs a retraction from an extension of
  the attaching map.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TopCat

noncomputable section

namespace Submission

universe u

variable {X : TopCat.{u}} {n : ℕ}

/-- The result of attaching one `n`-disk to `X` along `a : diskBoundary n ⟶ X`. -/
def cellAttachment (a : TopCat.diskBoundary n ⟶ X) : TopCat.{u} :=
  pushout a (TopCat.diskBoundaryIncl n)

/-- The inclusion of the original space into a one-cell attachment. -/
def cellAttachmentIncl (a : TopCat.diskBoundary n ⟶ X) : X ⟶ cellAttachment a :=
  pushout.inl a (TopCat.diskBoundaryIncl n)

/-- The original space embeds in a one-cell attachment. -/
instance (a : TopCat.diskBoundary n ⟶ X) : Mono (cellAttachmentIncl a) := by
  unfold cellAttachmentIncl
  exact mono_pushout_inl_topCat a (TopCat.diskBoundaryIncl n)

/-- The characteristic map of the disk in a one-cell attachment. -/
def cellAttachmentDisk (a : TopCat.diskBoundary n ⟶ X) :
    TopCat.disk n ⟶ cellAttachment a :=
  pushout.inr a (TopCat.diskBoundaryIncl n)

/-- The attaching square commutes. -/
@[reassoc]
theorem cellAttachment_condition (a : TopCat.diskBoundary n ⟶ X) :
    a ≫ cellAttachmentIncl a = TopCat.diskBoundaryIncl n ≫ cellAttachmentDisk a :=
  pushout.condition

/-- Define a map out of a one-cell attachment from compatible maps on `X` and the disk. -/
def cellAttachmentDesc (a : TopCat.diskBoundary n ⟶ X) {Y : TopCat.{u}}
    (f : X ⟶ Y) (g : TopCat.disk n ⟶ Y)
    (h : a ≫ f = TopCat.diskBoundaryIncl n ≫ g) :
    cellAttachment a ⟶ Y :=
  pushout.desc f g h

@[reassoc (attr := simp)]
theorem cellAttachmentIncl_desc (a : TopCat.diskBoundary n ⟶ X) {Y : TopCat.{u}}
    (f : X ⟶ Y) (g : TopCat.disk n ⟶ Y)
    (h : a ≫ f = TopCat.diskBoundaryIncl n ≫ g) :
    cellAttachmentIncl a ≫ cellAttachmentDesc a f g h = f :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem cellAttachmentDisk_desc (a : TopCat.diskBoundary n ⟶ X) {Y : TopCat.{u}}
    (f : X ⟶ Y) (g : TopCat.disk n ⟶ Y)
    (h : a ≫ f = TopCat.diskBoundaryIncl n ≫ g) :
    cellAttachmentDisk a ≫ cellAttachmentDesc a f g h = g :=
  pushout.inr_desc _ _ _

/-- Maps out of a one-cell attachment are determined by their restrictions to `X` and the disk. -/
theorem cellAttachment_hom_ext (a : TopCat.diskBoundary n ⟶ X) {Y : TopCat.{u}}
    {f g : cellAttachment a ⟶ Y}
    (hX : cellAttachmentIncl a ≫ f = cellAttachmentIncl a ≫ g)
    (hD : cellAttachmentDisk a ≫ f = cellAttachmentDisk a ≫ g) : f = g :=
  pushout.hom_ext hX hD

/-- An extension of the attaching map across the disk gives a map from the attachment back to
the original space. -/
def cellAttachmentRetractOfExtension (a : TopCat.diskBoundary n ⟶ X)
    (A : TopCat.disk n ⟶ X)
    (hA : TopCat.diskBoundaryIncl n ≫ A = a) : cellAttachment a ⟶ X :=
  cellAttachmentDesc a (𝟙 X) A (by simpa using hA.symm)

/-- The map obtained from an extension is a retraction of the original-space inclusion. -/
@[reassoc (attr := simp)]
theorem cellAttachmentIncl_retractOfExtension (a : TopCat.diskBoundary n ⟶ X)
    (A : TopCat.disk n ⟶ X)
    (hA : TopCat.diskBoundaryIncl n ≫ A = a) :
    cellAttachmentIncl a ≫ cellAttachmentRetractOfExtension a A hA = 𝟙 X := by
  rw [cellAttachmentRetractOfExtension, cellAttachmentIncl_desc]

end Submission
