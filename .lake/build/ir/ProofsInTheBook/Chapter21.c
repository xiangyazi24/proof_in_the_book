// Lean compiler output
// Module: ProofsInTheBook.Chapter21
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_once_cell_t lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference___closed__0;
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference(lean_object*, lean_object*);
static lean_object* _init_lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference(lean_object* v_f_3_, lean_object* v_x_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_5_ = lean_obj_once(&lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference___closed__0, &lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference___closed__0_once, _init_lp_proof__in__the__book_ProofsInTheBook_Chapter21_forwardDifference___closed__0);
v___x_6_ = lean_int_add(v_x_4_, v___x_5_);
lean_inc_ref(v_f_3_);
v___x_7_ = lean_apply_1(v_f_3_, v___x_6_);
v___x_8_ = lean_apply_1(v_f_3_, v_x_4_);
v___x_9_ = lean_int_sub(v___x_7_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v___x_7_);
return v___x_9_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter21(uint8_t builtin) {
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
