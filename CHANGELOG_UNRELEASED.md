# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_recl`

- in `sequences.v`:
  + lemma `nneseries_recl`

- in `measure.v`:
  + definition `subset_sigma_subadditive`
  + factory `isSubsetOuterMeasure`

- in file `classical_sets.v`
  + notations `\bigcup_(i >= n) F i` and `\bigcap_(i >= n) F i`
  + lemmas `bigcup_addn`, `bigcap_addn`

- in file `sequences.v`
  + lemma `nneseries_addn`
- in `lebesgue_integral.v`:
  + lemmas `integrableMl`, `integrableMr`
  
- in `topology.v`:
  + global instance `ball_filter`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pointedType`, `filteredType`, `topologicalType`,
      `uniformType`, `pseudoMetricType`
  + module `numFieldTopology` with an `Exports` submodule
    * many canonicals and coercions
  + global instance `Proper_nbhs'_regular_numFieldType`
- in `normedtype.v`:
  + definitions `ball_`, `pointed_of_zmodule`, `filtered_of_normedZmod`
  + lemmas `ball_norm_center`, `ball_norm_symmetric`, `ball_norm_triangle`
  + definition `pseudoMetric_of_normedDomain`
  + lemma `nbhs_ball_normE`
  + global instances `Proper_nbhs'_numFieldType`, `Proper_nbhs'_realType`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pseudoMetricNormedZmodType`, `normedModType`.
  + module `numFieldNormedType` with an `Exports` submodule
    * many canonicals and coercions
    * exports `Export numFieldTopology.Exports`
  + canonical `R_regular_completeType`, `R_regular_CompleteNormedModule`
- in `reals.v`:
  + lemmas `Rfloor_lt0`, `floor_lt0`, `ler_floor`, `ceil_gt0`, `ler_ceil`
- in `ereal.v`:
  + lemmas `ereal_ballN`, `le_ereal_ball`, `ereal_ball_ninfty_oversize`,
    `contract_ereal_ball_pinfty`, `expand_ereal_ball_pinfty`,
    `contract_ereal_ball_fin_le`, `contract_ereal_ball_fin_lt`,
    `expand_ereal_ball_fin_lt`, `ball_ereal_ball_fin_lt`, `ball_ereal_ball_fin_le`,
    `sumERFin`, `ereal_inf1`, `eqe_oppP`, `eqe_oppLRP`, `oppe_subset`,
    `ereal_inf_pinfty`
  + definition `er_map`
  + definition `er_map`
- in `classical_sets.v`:
  + notation `[disjoint ... & ..]`
  + lemmas `mkset_nil`, `bigcup_mkset`, `bigcup_nonempty`, `bigcup0`, `bigcup0P`,
    `subset_bigcup_r`, `eqbigcup_r`, `eq_set_inl`, `set_in_in`
- in `ereal.v`:
  + lemmas `adde_undefC`, `real_of_erD`, `fin_num_add_undef`, `addeK`,
    `subeK`, `subee`, `sube_le0`, `lee_sub`
  + lemmas `addeACA`, `muleC`, `mule1`, `mul1e`, `abseN`
  + enable notation `x \is a fin_num`
    * definition `fin_num`, fact `fin_num_key`, lemmas `fin_numE`, `fin_numP`
  + definition `dense` and lemma `denseNE`
- in `reals.v`:
  + lemmas `has_sup1`, `has_inf1`
- in `nngnum.v`:
  + instance `invr_nngnum`
- in `posnum.v`:
  + instance `posnum_nngnum`

- file `banach_steinhaus.v`:
  + lemma `le_closed_ball`
  + definition `Baire`
  + theorem `DeBaire`
  + definition `bounded_fun_norm`
  + lemma `bounded_landau`
  + definition `pointwise_bounded`
  + definition `uniform_bounded`
  + theorem `Banach_Steinhauss`

### Changed

### Renamed

- in `constructive_ereal.v`:
  + `gee_pmull` -> `gee_pMl`
  + `gee_addl` -> `geeDl`
  + `gee_addr` -> `geeDr`
  + `gte_addl` -> `gteDl`
  + `gte_addr` -> `gteDr`
  + `lte_subl_addr` -> `lteBlDr`
  + `lte_subl_addl` -> `lteBlDl`
  + `lte_subr_addr` -> `lteBrDr`
  + `lte_subr_addl` -> `lteBrDl`
  + `lee_subl_addr` -> `leeBlDr`
  + `lee_subl_addl` -> `leeBlDl`
  + `lee_subr_addr` -> `leeBrDr`
  + `lee_subr_addl` -> `leeBrDl`

- in `measure.v`:
  + `sub_additive` -> `subadditive`
  + `sigma_sub_additive` -> `measurable_subset_sigma_subadditive`
  + `content_sub_additive` -> `content_subadditive`
  + `ring_sigma_sub_additive` -> `ring_sigma_subadditive`
  + `Content_SubSigmaAdditive_isMeasure` -> `Content_SigmaSubAdditive_isMeasure`
  + `measure_sigma_sub_additive` -> `measure_sigma_subadditive`
  + `measure_sigma_sub_additive_tail` -> `measure_sigma_subadditive_tail`

### Generalized

- in `constructive_ereal.v`:
  + `gee_pMl` (was `gee_pmull`)

- in `sequences.v`:
  + lemmas `eseries0`, `nneseries_split`

### Deprecated

### Removed

- in `lebesgue_integral.v`:
  + `integrablerM`, `integrableMr` (were deprecated since version 0.6.4)

### Infrastructure

### Misc
