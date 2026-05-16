// Lean compiler output
// Module: ProofsInTheBook.Chapter10
// Imports: public import Init public meta import Init public import Mathlib
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_line_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_a_3_, v_line_2_);
v___x_5_ = lean_unbox(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg___lam__0___boxed(lean_object* v_inst_6_, lean_object* v_line_7_, lean_object* v_a_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg___lam__0(v_inst_6_, v_line_7_, v_a_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg(lean_object* v_points_11_, lean_object* v_inst_12_, lean_object* v_line_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; 
v___f_14_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_14_, 0, v_inst_12_);
lean_closure_set(v___f_14_, 1, v_line_13_);
v___x_15_ = lp_mathlib_Multiset_filter___redArg(v___f_14_, v_points_11_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine(lean_object* v_Point_16_, lean_object* v_Line_17_, lean_object* v_inst_18_, lean_object* v_points_19_, lean_object* v_onLine_20_, lean_object* v_inst_21_, lean_object* v_line_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___redArg(v_points_19_, v_inst_21_, v_line_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine___boxed(lean_object* v_Point_24_, lean_object* v_Line_25_, lean_object* v_inst_26_, lean_object* v_points_27_, lean_object* v_onLine_28_, lean_object* v_inst_29_, lean_object* v_line_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_proof__in__the__book_ProofsInTheBook_Chapter10_pointsOnLine(v_Point_24_, v_Line_25_, v_inst_26_, v_points_27_, v_onLine_28_, v_inst_29_, v_line_30_);
lean_dec_ref(v_inst_26_);
return v_res_31_;
}
}
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg___lam__0(lean_object* v_inst_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_fst_34_; lean_object* v_snd_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_fst_34_ = lean_ctor_get(v_a_33_, 0);
lean_inc(v_fst_34_);
v_snd_35_ = lean_ctor_get(v_a_33_, 1);
lean_inc(v_snd_35_);
lean_dec_ref(v_a_33_);
v___x_36_ = lean_apply_2(v_inst_32_, v_fst_34_, v_snd_35_);
v___x_37_ = lean_unbox(v___x_36_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; 
v___x_38_ = 1;
return v___x_38_;
}
else
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg___lam__0___boxed(lean_object* v_inst_40_, lean_object* v_a_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg___lam__0(v_inst_40_, v_a_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg(lean_object* v_points_44_, lean_object* v_lines_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___f_47_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_47_, 0, v_inst_46_);
v___x_48_ = lp_mathlib_Multiset_product___redArg(v_points_44_, v_lines_45_);
v___x_49_ = lp_mathlib_Multiset_filter___redArg(v___f_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs(lean_object* v_Point_50_, lean_object* v_Line_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_points_54_, lean_object* v_lines_55_, lean_object* v_onLine_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___redArg(v_points_54_, v_lines_55_, v_inst_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs___boxed(lean_object* v_Point_59_, lean_object* v_Line_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_points_63_, lean_object* v_lines_64_, lean_object* v_onLine_65_, lean_object* v_inst_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_proof__in__the__book_ProofsInTheBook_Chapter10_offLinePairs(v_Point_59_, v_Line_60_, v_inst_61_, v_inst_62_, v_points_63_, v_lines_64_, v_onLine_65_, v_inst_66_);
lean_dec_ref(v_inst_62_);
lean_dec_ref(v_inst_61_);
return v_res_67_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter10(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
