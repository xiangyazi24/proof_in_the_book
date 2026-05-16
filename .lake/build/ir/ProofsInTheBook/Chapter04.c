// Lean compiler output
// Module: ProofsInTheBook.Chapter04
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_SimplexCategory_instFintypeToTypeOrderHomFinHAddNatLenOfNat(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Fintype_ofEquiv___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__0 = (const lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__0_value;
static const lean_closure_object lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__1 = (const lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__1_value;
static const lean_ctor_object lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__0_value),((lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__1_value)}};
static const lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__2 = (const lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__2_value;
static lean_once_cell_t lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__3;
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_canonicalTriple___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_canonicalTriple(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___lam__0(lean_object*);
static const lean_closure_object lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__0 = (const lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__0_value;
static const lean_ctor_object lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__0_value),((lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__0_value)}};
static const lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__1 = (const lean_object*)&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__1_value;
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__0(lean_object* v_t_1_){
_start:
{
lean_object* v_x_2_; lean_object* v_y_3_; lean_object* v_z_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_x_2_ = lean_ctor_get(v_t_1_, 0);
v_y_3_ = lean_ctor_get(v_t_1_, 1);
v_z_4_ = lean_ctor_get(v_t_1_, 2);
lean_inc(v_z_4_);
lean_inc(v_y_3_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_y_3_);
lean_ctor_set(v___x_5_, 1, v_z_4_);
lean_inc(v_x_2_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_x_2_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__0___boxed(lean_object* v_t_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__0(v_t_7_);
lean_dec_ref(v_t_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__1(lean_object* v_u_9_){
_start:
{
lean_object* v_snd_10_; lean_object* v_fst_11_; lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v___x_14_; 
v_snd_10_ = lean_ctor_get(v_u_9_, 1);
v_fst_11_ = lean_ctor_get(v_u_9_, 0);
v_fst_12_ = lean_ctor_get(v_snd_10_, 0);
v_snd_13_ = lean_ctor_get(v_snd_10_, 1);
lean_inc(v_snd_13_);
lean_inc(v_fst_12_);
lean_inc(v_fst_11_);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v_fst_11_);
lean_ctor_set(v___x_14_, 1, v_fst_12_);
lean_ctor_set(v___x_14_, 2, v_snd_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__1___boxed(lean_object* v_u_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__1(v_u_15_);
lean_dec_ref(v_u_15_);
return v_res_16_;
}
}
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__2(lean_object* v_p_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_fst_19_; lean_object* v_snd_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_fst_19_ = lean_ctor_get(v_a_18_, 0);
v_snd_20_ = lean_ctor_get(v_a_18_, 1);
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = lean_nat_dec_lt(v___x_21_, v_fst_19_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
lean_object* v_fst_23_; lean_object* v_snd_24_; uint8_t v___x_25_; 
v_fst_23_ = lean_ctor_get(v_snd_20_, 0);
v_snd_24_ = lean_ctor_get(v_snd_20_, 1);
v___x_25_ = lean_nat_dec_lt(v___x_21_, v_fst_23_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = lean_nat_dec_lt(v___x_21_, v_snd_24_);
if (v___x_26_ == 0)
{
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = lean_nat_pow(v_fst_19_, v___x_27_);
v___x_29_ = lean_unsigned_to_nat(4u);
v___x_30_ = lean_nat_mul(v___x_29_, v_fst_23_);
v___x_31_ = lean_nat_mul(v___x_30_, v_snd_24_);
lean_dec(v___x_30_);
v___x_32_ = lean_nat_add(v___x_28_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_28_);
v___x_33_ = lean_nat_dec_eq(v___x_32_, v_p_17_);
lean_dec(v___x_32_);
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__2___boxed(lean_object* v_p_34_, lean_object* v_a_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__2(v_p_34_, v_a_35_);
lean_dec_ref(v_a_35_);
lean_dec(v_p_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
static lean_object* _init_lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__3(void){
_start:
{
lean_object* v_e_43_; lean_object* v___x_44_; 
v_e_43_ = ((lean_object*)(lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__2));
v___x_44_ = lp_mathlib_Equiv_symm___redArg(v_e_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype(lean_object* v_p_45_){
_start:
{
lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
lean_inc(v_p_45_);
v___f_46_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___lam__2___boxed), 2, 1);
lean_closure_set(v___f_46_, 0, v_p_45_);
v___x_47_ = lp_mathlib_SimplexCategory_instFintypeToTypeOrderHomFinHAddNatLenOfNat(v_p_45_);
lean_dec(v_p_45_);
lean_inc_n(v___x_47_, 2);
v___x_48_ = lp_mathlib_Multiset_product___redArg(v___x_47_, v___x_47_);
v___x_49_ = lp_mathlib_Multiset_product___redArg(v___x_47_, v___x_48_);
v___x_50_ = lp_mathlib_Subtype_fintype___redArg(v___f_46_, v___x_49_);
v___x_51_ = lean_obj_once(&lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__3, &lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__3_once, _init_lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_instFintype___closed__3);
v___x_52_ = lp_mathlib_Fintype_ofEquiv___redArg(v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_canonicalTriple___redArg(lean_object* v_k_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
lean_ctor_set(v___x_55_, 2, v_k_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_canonicalTriple(lean_object* v_k_56_, lean_object* v_hk_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_canonicalTriple___redArg(v_k_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne___redArg(lean_object* v_t_59_){
_start:
{
lean_object* v_x_60_; lean_object* v_y_61_; lean_object* v_z_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_74_; 
v_x_60_ = lean_ctor_get(v_t_59_, 0);
v_y_61_ = lean_ctor_get(v_t_59_, 1);
v_z_62_ = lean_ctor_get(v_t_59_, 2);
v_isSharedCheck_74_ = !lean_is_exclusive(v_t_59_);
if (v_isSharedCheck_74_ == 0)
{
v___x_64_ = v_t_59_;
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_z_62_);
lean_inc(v_y_61_);
lean_inc(v_x_60_);
lean_dec(v_t_59_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_66_ = lean_unsigned_to_nat(2u);
v___x_67_ = lean_nat_mul(v___x_66_, v_z_62_);
v___x_68_ = lean_nat_add(v_x_60_, v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = lean_nat_sub(v_y_61_, v_x_60_);
lean_dec(v_x_60_);
lean_dec(v_y_61_);
v___x_70_ = lean_nat_sub(v___x_69_, v_z_62_);
lean_dec(v___x_69_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 2, v___x_70_);
lean_ctor_set(v___x_64_, 1, v_z_62_);
lean_ctor_set(v___x_64_, 0, v___x_68_);
v___x_72_ = v___x_64_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_z_62_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne(lean_object* v_p_75_, lean_object* v_t_76_, lean_object* v_h_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne___redArg(v_t_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne___boxed(lean_object* v_p_79_, lean_object* v_t_80_, lean_object* v_h_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne(v_p_79_, v_t_80_, v_h_81_);
lean_dec(v_p_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo___redArg(lean_object* v_t_83_){
_start:
{
lean_object* v_x_84_; lean_object* v_y_85_; lean_object* v_z_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_98_; 
v_x_84_ = lean_ctor_get(v_t_83_, 0);
v_y_85_ = lean_ctor_get(v_t_83_, 1);
v_z_86_ = lean_ctor_get(v_t_83_, 2);
v_isSharedCheck_98_ = !lean_is_exclusive(v_t_83_);
if (v_isSharedCheck_98_ == 0)
{
v___x_88_ = v_t_83_;
v_isShared_89_ = v_isSharedCheck_98_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_z_86_);
lean_inc(v_y_85_);
lean_inc(v_x_84_);
lean_dec(v_t_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_98_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_90_ = lean_unsigned_to_nat(2u);
v___x_91_ = lean_nat_mul(v___x_90_, v_y_85_);
v___x_92_ = lean_nat_sub(v___x_91_, v_x_84_);
lean_dec(v___x_91_);
v___x_93_ = lean_nat_add(v_x_84_, v_z_86_);
lean_dec(v_z_86_);
lean_dec(v_x_84_);
v___x_94_ = lean_nat_sub(v___x_93_, v_y_85_);
lean_dec(v___x_93_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v___x_94_);
lean_ctor_set(v___x_88_, 0, v___x_92_);
v___x_96_ = v___x_88_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_y_85_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo(lean_object* v_p_99_, lean_object* v_t_100_, lean_object* v_hleft_101_, lean_object* v_hright_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo___redArg(v_t_100_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo___boxed(lean_object* v_p_104_, lean_object* v_t_105_, lean_object* v_hleft_106_, lean_object* v_hright_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo(v_p_104_, v_t_105_, v_hleft_106_, v_hright_107_);
lean_dec(v_p_104_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree___redArg(lean_object* v_t_109_){
_start:
{
lean_object* v_x_110_; lean_object* v_y_111_; lean_object* v_z_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_124_; 
v_x_110_ = lean_ctor_get(v_t_109_, 0);
v_y_111_ = lean_ctor_get(v_t_109_, 1);
v_z_112_ = lean_ctor_get(v_t_109_, 2);
v_isSharedCheck_124_ = !lean_is_exclusive(v_t_109_);
if (v_isSharedCheck_124_ == 0)
{
v___x_114_ = v_t_109_;
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_z_112_);
lean_inc(v_y_111_);
lean_inc(v_x_110_);
lean_dec(v_t_109_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = lean_nat_mul(v___x_116_, v_y_111_);
v___x_118_ = lean_nat_sub(v_x_110_, v___x_117_);
lean_dec(v___x_117_);
v___x_119_ = lean_nat_sub(v_x_110_, v_y_111_);
lean_dec(v_x_110_);
v___x_120_ = lean_nat_add(v___x_119_, v_z_112_);
lean_dec(v_z_112_);
lean_dec(v___x_119_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 2, v_y_111_);
lean_ctor_set(v___x_114_, 1, v___x_120_);
lean_ctor_set(v___x_114_, 0, v___x_118_);
v___x_122_ = v___x_114_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_y_111_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree(lean_object* v_p_125_, lean_object* v_t_126_, lean_object* v_h_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree___redArg(v_t_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree___boxed(lean_object* v_p_129_, lean_object* v_t_130_, lean_object* v_h_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree(v_p_129_, v_t_130_, v_h_131_);
lean_dec(v_p_129_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo___redArg(lean_object* v_t_133_){
_start:
{
lean_object* v_x_134_; lean_object* v_y_135_; lean_object* v_z_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_x_134_ = lean_ctor_get(v_t_133_, 0);
v_y_135_ = lean_ctor_get(v_t_133_, 1);
v_z_136_ = lean_ctor_get(v_t_133_, 2);
v___x_137_ = lean_nat_sub(v_y_135_, v_z_136_);
v___x_138_ = lean_nat_dec_lt(v_x_134_, v___x_137_);
lean_dec(v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(2u);
v___x_140_ = lean_nat_mul(v___x_139_, v_y_135_);
v___x_141_ = lean_nat_dec_lt(v_x_134_, v___x_140_);
lean_dec(v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchThree___redArg(v_t_133_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchTwo___redArg(v_t_133_);
return v___x_143_;
}
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_branchOne___redArg(v_t_133_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo(lean_object* v_p_145_, lean_object* v_hp_146_, lean_object* v_hp2_147_, lean_object* v_t_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo___redArg(v_t_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo___boxed(lean_object* v_p_150_, lean_object* v_hp_151_, lean_object* v_hp2_152_, lean_object* v_t_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_zagierMapOfPrimeNeTwo(v_p_150_, v_hp_151_, v_hp2_152_, v_t_153_);
lean_dec(v_p_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___lam__0(lean_object* v_t_155_){
_start:
{
lean_object* v_x_156_; lean_object* v_y_157_; lean_object* v_z_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_x_156_ = lean_ctor_get(v_t_155_, 0);
v_y_157_ = lean_ctor_get(v_t_155_, 1);
v_z_158_ = lean_ctor_get(v_t_155_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v_t_155_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v_t_155_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_z_158_);
lean_inc(v_y_157_);
lean_inc(v_x_156_);
lean_dec(v_t_155_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 2, v_y_157_);
lean_ctor_set(v___x_160_, 1, v_z_158_);
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_x_156_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_z_158_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_y_157_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ(lean_object* v_p_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___closed__1));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ___boxed(lean_object* v_p_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = lp_proof__in__the__book_ProofsInTheBook_Chapter04_ZagierTriple_swapYZ(v_p_171_);
lean_dec(v_p_171_);
return v_res_172_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter04(uint8_t builtin) {
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
