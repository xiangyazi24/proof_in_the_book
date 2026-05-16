// Lean compiler output
// Module: ProofsInTheBook.Chapter39
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
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_powerset___redArg(lean_object*);
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_kneserGraph(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_kneserGraph___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex___lam__0(lean_object* v_k_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = l_List_lengthTR___redArg(v_a_2_);
v___x_4_ = lean_nat_dec_eq(v___x_3_, v_k_1_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex___lam__0___boxed(lean_object* v_k_5_, lean_object* v_a_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex___lam__0(v_k_5_, v_a_6_);
lean_dec(v_a_6_);
lean_dec(v_k_5_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex(lean_object* v_n_9_, lean_object* v_k_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_11_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter39_instFintypeKneserVertex___lam__0___boxed), 2, 1);
lean_closure_set(v___f_11_, 0, v_k_10_);
v___x_12_ = l_List_finRange(v_n_9_);
v___x_13_ = lp_mathlib_Finset_powerset___redArg(v___x_12_);
v___x_14_ = lp_mathlib_Subtype_fintype___redArg(v___f_11_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___redArg(lean_object* v_n_15_, lean_object* v_a_16_, lean_object* v_b_17_){
_start:
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_18_, 0, v_n_15_);
v___x_19_ = l_List_decidablePerm___redArg(v___x_18_, v_a_16_, v_b_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___redArg___boxed(lean_object* v_n_20_, lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___redArg(v_n_20_, v_a_21_, v_b_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex(lean_object* v_n_25_, lean_object* v_k_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___redArg(v_n_25_, v_a_27_, v_b_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex___boxed(lean_object* v_n_30_, lean_object* v_k_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = lp_proof__in__the__book_ProofsInTheBook_Chapter39_instDecidableEqKneserVertex(v_n_30_, v_k_31_, v_a_32_, v_b_33_);
lean_dec(v_k_31_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_kneserGraph(lean_object* v_n_36_, lean_object* v_k_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter39_kneserGraph___boxed(lean_object* v_n_39_, lean_object* v_k_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_proof__in__the__book_ProofsInTheBook_Chapter39_kneserGraph(v_n_39_, v_k_40_);
lean_dec(v_k_40_);
lean_dec(v_n_39_);
return v_res_41_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter39(uint8_t builtin) {
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
