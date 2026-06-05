import ProofsInTheBook.Chapter01
import ProofsInTheBook.Chapter02
import ProofsInTheBook.Chapter03
import ProofsInTheBook.Chapter04
import ProofsInTheBook.Chapter05
import ProofsInTheBook.Chapter06
import ProofsInTheBook.Chapter07
import ProofsInTheBook.Chapter08
import ProofsInTheBook.Chapter09
import ProofsInTheBook.ConeLemma
import ProofsInTheBook.SectorSum
import ProofsInTheBook.PearlLemma
import ProofsInTheBook.TetPearls
import ProofsInTheBook.Chapter10
import ProofsInTheBook.Chapter11
import ProofsInTheBook.Chapter12
import ProofsInTheBook.ArmLemma
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Chapter14
import ProofsInTheBook.Chapter15
import ProofsInTheBook.Chapter16
import ProofsInTheBook.Chapter17
import ProofsInTheBook.Chapter18
import ProofsInTheBook.Chapter19
import ProofsInTheBook.Chapter20
import ProofsInTheBook.Chapter21
import ProofsInTheBook.Chapter22
import ProofsInTheBook.Chapter23
import ProofsInTheBook.Chapter24
import ProofsInTheBook.Chapter25
import ProofsInTheBook.Chapter26
import ProofsInTheBook.Chapter27
import ProofsInTheBook.Chapter28
import ProofsInTheBook.Chapter29
import ProofsInTheBook.Chapter30
import ProofsInTheBook.Chapter31
import ProofsInTheBook.Chapter32
import ProofsInTheBook.Chapter33
import ProofsInTheBook.Chapter34
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapBoundary
import ProofsInTheBook.PlanarMapNearTriangulation
import ProofsInTheBook.PlanarMapBoundaryFan
import ProofsInTheBook.PlanarMapFilteredRotation
import ProofsInTheBook.PlanarMapChordSplitData
import ProofsInTheBook.PlanarMapBoundaryDelete
import ProofsInTheBook.PlanarMapChordSplit
import ProofsInTheBook.SimpleGraphBlocks
import ProofsInTheBook.ListColoring
import ProofsInTheBook.Chapter35
import ProofsInTheBook.PolygonSubstrate
import ProofsInTheBook.PolygonDiagonal
import ProofsInTheBook.Chapter36
import ProofsInTheBook.Chapter37
import ProofsInTheBook.Chapter38
import ProofsInTheBook.Chapter39
import ProofsInTheBook.Chapter40
-- Chapter 20 (Monsky) faithful dissection theorem `monsky_dissection`
-- (unconditional; supersedes the edge-to-edge `RealEqualAreaUnitSquareTriangulation` escape).
import ProofsInTheBook.Chapter20DissectionFinal
-- Chapter 39 (Kneser) faithful Tucker lemma `tuckerLemma_pos` + unconditional
-- `chapter39_unconditional` (discharges the Tucker hypothesis of `chapter39`).
import ProofsInTheBook.Chapter39Tucker
-- Planar-graph infrastructure (the Mathlib hole): combinatorial maps, Euler characteristic,
-- the Euler consequences (E ≤ 3V-6, min-degree ≤ 5), and the simple-graph embedding layer.
-- Backs Chapter 12 (Platonic from Euler) and the Chapter 35 five-color development.
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PlaneSimpleGraph
-- Chapter 35 (5-color) WIP: vertex-deletion machinery on combinatorial maps (Perm.deleteSet splice,
-- deleteVertex + V/E counts). Euler-preservation + Kempe + coloring still to come.
import ProofsInTheBook.PlanarMapDelete
-- Chapter 33 (Smetaniuk/Evans) scaffold: triangular invariant + back-diagonal construction + reduction
-- to the cunning-switching core `SmetBackDiagonalCompletableCore` (the remaining hard lemma).
import ProofsInTheBook.Chapter33Smetaniuk
import ProofsInTheBook.Chapter33Ryser
import ProofsInTheBook.Chapter33Unconditional

-- Chapter 22 (Gurvits) WIP: capacity constant + telescoping (n!/n^n) + univariate Gurvits analytic
-- crux + capacity iteration; real-stable polynomial framework. Reduced to the Lieb-Sokal ∂-closure.
import ProofsInTheBook.Chapter22Gurvits
import ProofsInTheBook.Chapter22Stable
