(pbook wave-3 retry, 2026-06-10, via tab paste) A2 SUBSTRATE INVENTORY:
- rotS2 = Rodrigues lift; recorded: rot_axis, inner_rot_axis, inner_rot_rot, norm_rot, sDist_rotS2,
  tangentTo_rotS2, sphAngle_rotS2, inner_rot_tangent (cosine-side planar rotation only).
- openedInteriorJointAngle: apex A(k+1), incoming jointPrev FIXED, outgoing jointNext ROTATED;
  zero lemma exists. Sign convention: right-hand about axis (w moves toward cross k w for θ > 0).
- NO OpeningDirectionPositive exists; interiorCombined monitors only supports + target slack.
- Provable now: only the cosine formula cos(opened) = cosδ·cosγ + sinδ·orientationTerm.
- MISSING prerequisites (now fully specified): tangentTo_axis_rotS2 (one-line from tangentTo_rotS2 +
  rot_axis) and sphAngle_axis_rotS2_eq_add_of_oriented with horient : ⟪u, cross(axis, w)⟫ =
  −‖u‖‖w‖·sin γ (THE hidden orientation hypothesis = the correct definition of
  OpeningDirectionPositive; opposite sign ⟹ conclusion γ − δ or rotate by −δ).
- Branch control: Real.arccos_cos on [0, π] + sphAngle_nonneg/le_pi + jointAngle_lt_pi (FFCT3).
- Full typechecking statement + 10-line skeleton archived in session log; main blocker is
  supplying horient from the δ*-machinery's direction choice (definitional, not topological).
