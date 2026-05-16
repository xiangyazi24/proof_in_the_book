// Lean compiler output
// Module: ProofsInTheBook.Chapter23
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
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___redArg___lam__0(lean_object* v_a_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_a_1_, v_i_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___redArg(lean_object* v_a_4_, lean_object* v_s_5_){
_start:
{
lean_object* v___f_6_; lean_object* v___x_7_; 
v___f_6_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v_a_4_);
v___x_7_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v_s_5_, v___f_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum(lean_object* v_n_8_, lean_object* v_a_9_, lean_object* v_s_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___redArg(v_a_9_, v_s_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum___boxed(lean_object* v_n_12_, lean_object* v_a_13_, lean_object* v_s_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_proof__in__the__book_ProofsInTheBook_Chapter23_subsetSum(v_n_12_, v_a_13_, v_s_14_);
lean_dec(v_n_12_);
return v_res_15_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter23(uint8_t builtin) {
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
