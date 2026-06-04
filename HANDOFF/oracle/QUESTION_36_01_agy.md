I need to upgrade the `chapter36` theorem in `ProofsInTheBook/Chapter36.lean` to a Tier 1 conditional form.

The current file has:
- `exists_small_guard_color_class` (which proves that given a triangulation where every triangle has all 3 colors, there exists a set of guards of size ≤ `vertices.card / 3` that hits every triangle).
- A dummy `art_gallery_theorem` placeholder.
- A dummy `chapter36` testing `min red (min green blue) ≤ (red+green+blue)/3`.

The user requested: "主定理 chapter36 取 'TriangulationCertificate' / 'ArtGalleryWitness' 作 hypothesis, 用现有基础设施推出 chapter 主结论 (⌊n/3⌋ guards suffice for simple polygon n vertices)."

Could you provide the exact Lean 4 code for the Tier 1 `chapter36` theorem and `ArtGalleryWitness` structure? Please provide the exact code so I can replace the placeholders cleanly.
