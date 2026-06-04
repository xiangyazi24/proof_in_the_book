# QUESTION 03 01: 定理声明 + 证明策略双重阻塞

## (i) 试过什么

1. 读了 Chapter03.lean 全部 3617 行（结构理解，非逐行审阅）
2. 提取了书 PDF Ch03 全文（约 4 页，1269-1520 行 raw text）
3. 搜了 Mathlib：
   - `Nat.factorization_choose_le_one` (条件 `n < p^2`，即 p > √n)
   - `padicValNat_choose` (Kummer's theorem)
   - `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`
   - 已有 `sylvester_general` (0 sorry) + `chapter03_binomials_coefficients_never_powers` (0 sorry)

4. 验证了关键反例：
   - C(100, 2) = 4950 = 2 * 3^2 * 5^2 * 11，v_3 = 2，p=3 > k=2，2k=4 ≤ 100
   - 所以 "p > k ⇒ v_p(C(n,k)) ≤ 1" 是 **false**

## (ii) 阻塞点

### 阻塞 A：定理声明（k ≥ 2 是错的）

你给的定理声明：
```
theorem chapter03_erdos_selfridge (n k l : ℕ) (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (hl : 2 ≤ l) (m : ℕ) : n.choose k ≠ m ^ l
```

**反例 1**：C(50, 2) = 1225 = 35^2，k=2, n=50, l=2, m=35
**反例 2**：C(50, 3) = 19600 = 140^2，k=3, n=50, l=2, m=140

这些反例在书里**明确讨论**了（pp. 13-14）：
- k=2 有无穷多 l=2 解（书上给了递推构造）
- k=3 有唯一解 C(50,3) = 140^2（l=2）
- 书上定理条件是 **k ≥ 4**（且 k ≤ n-4，由 n ≥ 2k + k≥4 自动满足）

### 阻塞 B：证明策略（v_p ≤ 1 路线不可行）

你的 proof sketch 步骤 5（p > k ⇒ v_p(C(n,k)) ≤ 1）被 C(100,2) 反例证伪。

- `Nat.factorization_choose_le_one` 的 condition 是 `n < p^2`（p > √n），不是 `k < p`
- Sylvester 给 p > k，不能保证 p > √n

**书上真正的证明**（4 步，约 200-300 行 Lean）：

1. Sylvester: ∃ p > k, p | C(n,k). ∵ C(n,k) = m^l, p^l | n(n-1)...(n-k+1). ∵ p > k, 唯一 n-i 含 p ⇒ p^l | n-i ⇒ n ≥ p^l > k^l ≥ k^2.
2. Write n-j = a_j * m_j^l where a_j is l-th-power-free. Show a_i ≠ a_j (via algebraic inequality).
3. The a_i's are {1,2,...,k} in some order (crux: via Legendre, bounding, and gcd argument).
4. l=2 case: k ≥ 4 ⇒ some a_i = 4, but a_i's squarefree ⇒ contradiction. l ≥ 3 case: use n-i_1=m_1^l, n-i_2=2*m_2^l, n-i_3=4*m_3^l with m_2^2 ≠ m_1 m_3.

### 阻塞 C：额外条件 k ≤ n-4

书定理有条件 4 ≤ k ≤ n-4。n ≥ 2k + k≥4 ⇒ n-4 ≥ 2k-4 ≥ k ✓，所以 `(hk : 4 ≤ k) (hn : 2*k ≤ n)` 足够。

但 k=4, n=8 时 n-4=4=k，边界检查：C(8,4) = 70 = 2*5*7，非完全幂，没问题。

## (iii) 要你帮什么

1. **定理声明拍板**：确认用 `(hk : 4 ≤ k)` 而非 `(hk : 2 ≤ k)`？书定理明确针对 k ≥ 4。k=2 有无穷多平方解，k=3 有唯一解 C(50,3)=140^2，都不属于 "almost never" 的结论范围。

2. **证明策略确认**：书上的 4-step proof（a_j 分解 + squarefree + 1..k bijection） vs 你有没有简化的替代路线？如果可以简化（利用现有 3600 行中已经证明的 infra），请指示方向。

3. **命名**：定理名叫 `chapter03_erdos_selfridge` 还是 `chapter03_erdos`（书 attribution 是 Erdős 1951，非 Erdős–Selfridge 1975）？书 Ref [2] 是 Erdős 1951 "On a diophantine equation"。

等 reply 后我会直接进入实现。
