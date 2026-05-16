// Lean compiler output
// Module: ProofsInTheBook.Chapter16
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg___lam__0(lean_object* v_color_1_, lean_object* v_c_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_1(v_color_1_, v_a_3_);
v___x_5_ = lean_nat_dec_eq(v___x_4_, v_c_2_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg___lam__0___boxed(lean_object* v_color_6_, lean_object* v_c_7_, lean_object* v_a_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg___lam__0(v_color_6_, v_c_7_, v_a_8_);
lean_dec(v_c_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg(lean_object* v_points_11_, lean_object* v_color_12_, lean_object* v_c_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; 
v___f_14_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_14_, 0, v_color_12_);
lean_closure_set(v___f_14_, 1, v_c_13_);
v___x_15_ = lp_mathlib_Multiset_filter___redArg(v___f_14_, v_points_11_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass(lean_object* v_00_u03b1_16_, lean_object* v_d_17_, lean_object* v_points_18_, lean_object* v_color_19_, lean_object* v_c_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___redArg(v_points_18_, v_color_19_, v_c_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass___boxed(lean_object* v_00_u03b1_22_, lean_object* v_d_23_, lean_object* v_points_24_, lean_object* v_color_25_, lean_object* v_c_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_proof__in__the__book_ProofsInTheBook_Chapter16_colorClass(v_00_u03b1_22_, v_d_23_, v_points_24_, v_color_25_, v_c_26_);
lean_dec(v_d_23_);
return v_res_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter16(uint8_t builtin) {
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
