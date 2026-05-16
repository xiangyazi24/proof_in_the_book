// Lean compiler output
// Module: ProofsInTheBook.Chapter09
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
lean_object* lp_mathlib_TensorProduct_tmul___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Int_instCommSemiring;
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
extern lean_object* lp_mathlib_Real_instAddCommGroup;
lean_object* lp_mathlib_TensorProduct_addMonoid___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnEdge___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnEdge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnEdge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnEdge___redArg(lean_object* v_length_1_, lean_object* v_angle_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lp_mathlib_TensorProduct_tmul___redArg(v_length_1_, v_angle_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnEdge(lean_object* v_Angle_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_length_7_, lean_object* v_angle_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lp_mathlib_TensorProduct_tmul___redArg(v_length_7_, v_angle_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnEdge___boxed(lean_object* v_Angle_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_length_13_, lean_object* v_angle_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnEdge(v_Angle_10_, v_inst_11_, v_inst_12_, v_length_13_, v_angle_14_);
lean_dec(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant___redArg___lam__0(lean_object* v_length_16_, lean_object* v_angle_17_, lean_object* v_e_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc(v_e_18_);
v___x_19_ = lean_apply_1(v_length_16_, v_e_18_);
v___x_20_ = lean_apply_1(v_angle_17_, v_e_18_);
v___x_21_ = lp_mathlib_TensorProduct_tmul___redArg(v___x_19_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant___redArg(lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_edges_24_, lean_object* v_length_25_, lean_object* v_angle_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_zsmul_30_; lean_object* v_toAddMonoid_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_27_ = lp_mathlib_Int_instCommSemiring;
v___x_28_ = lp_mathlib_Real_instAddCommMonoid;
v___x_29_ = lp_mathlib_Real_instAddCommGroup;
v_zsmul_30_ = lean_ctor_get(v___x_29_, 3);
v_toAddMonoid_31_ = lean_ctor_get(v_inst_22_, 0);
lean_inc_ref(v_toAddMonoid_31_);
lean_dec_ref(v_inst_22_);
v___f_32_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant___redArg___lam__0), 3, 2);
lean_closure_set(v___f_32_, 0, v_length_25_);
lean_closure_set(v___f_32_, 1, v_angle_26_);
lean_inc(v_zsmul_30_);
v___x_33_ = lp_mathlib_TensorProduct_addMonoid___redArg(v___x_27_, v___x_28_, v_toAddMonoid_31_, v_zsmul_30_, v_inst_23_);
v___x_34_ = lp_mathlib_Finset_sum___redArg(v___x_33_, v_edges_24_, v___f_32_);
lean_dec_ref(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant(lean_object* v_Edge_35_, lean_object* v_Angle_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_edges_39_, lean_object* v_length_40_, lean_object* v_angle_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_proof__in__the__book_ProofsInTheBook_Chapter09_dehnInvariant___redArg(v_inst_37_, v_inst_38_, v_edges_39_, v_length_40_, v_angle_41_);
return v___x_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter09(uint8_t builtin) {
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
