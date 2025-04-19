from Crypto.Util.number import getPrime, getRandomRange, isPrime
from typing import List, Tuple
from util import mod_exp, generate_parameters
import random



def simple_k_shuffle_proof_II(p : int, q : int, g : int,
  X : List[int], Y : List[int], x : List[int], y : List[int],
  c : int, d : int, beta : int, tau : int, lam : int, t : int, 
  gamma : int) -> Tuple[int, int, List[int], List[int]]:
  k = len(X)
  assert len(Y) == k
  assert len(x) == k
  assert len(y) == k

  # randomness is passed as parameters. 
  # Step 1: Prover generates β, τ and computes B, T
  # beta = getRandomRange(1, q)
  # tau = getRandomRange(1, q)
  B = mod_exp(g, beta, p)  # B = g^β
  T = mod_exp(g, tau, p)   # T = g^τ

  # Step 2: V generates a random λ from Zq and reveals it to P.
  # lam = getRandomRange(1, q)


  # Step 3: Prover computes s = β + λτ - (d/c)^k mod q
  d_over_c =(d * mod_exp(c, -1, q)) % q  # d/c mod q
  s = (beta + lam * tau - mod_exp(d_over_c, k, q)) % q

  # Step 4: Verifier sends challenge t (simulated)
  # t = getRandomRange(1, q)

  # Step 5: Prover computes Compute U = D^t, W = C^t, X̃ = X/U, Ŷ = Y/W
  C = mod_exp(g, c, p)  # C = g^c
  D = mod_exp(g, d, p)  # D = g^d
  U = mod_exp(D, t, p)  # U = D^t
  W = mod_exp(C, t, p)  # W = C^t

  X_hat = [(X[i] * mod_exp(U, -1, p)) % p for i in range(k)]  # X̃_i = X_i / U
  Y_hat = [(Y[i] * mod_exp(W, -1, p)) % p for i in range(k)]  # Ŷ_i = Y_i / W

  # Step 6: Prover generates θ_1,...,θ_k and computes A_1,...,A_{k+1}
  theta = [getRandomRange(1, q) for _ in range(k)]
  A = []
  A.append(mod_exp(Y_hat[0], theta[0], p))  # A_1 = Ŷ_1^{θ_1}
  for i in range(1, k): 
    A.append(mod_exp(X_hat[i], theta[i-1], p) * mod_exp(Y_hat[i], theta[i], p) % p)  # A_i = X̃_i^{θ_{i-1}} * Ŷ_i^{θ_i}
  A.append(mod_exp(g, theta[k-1], p))

  # Step 7: Verifier sends challenge γ (simulated)
  # gamma = getRandomRange(1, q)

  # Step 8: Prover computes r_1,...,r_k
  r = []
  sign = -gamma
  acc = 1
  for i in range(k):
    # Compute r_i = θ_i + sign * acc (mod q)
    acc = (acc * (((x[i] - d * t) % q) * mod_exp((y[i] - c * t) % q, -1, q))) % q  # acc *= (x_i / y_i)
    r_i = (theta[i] + sign * acc) % q
    r.append(r_i)
    sign = -sign
  r_k = (theta[-1] + ((-1)**k) * gamma * (beta + lam * tau - s)) % q
  r.append(r_k)

  return C, D, B, T, s, A, r


def simple_k_shuffle_verify_II(p : int, X : List[int], Y : List[int], 
  B : int, T : int, s : int,
  C : int, D : int, A : List[int], r : List[int], lam : int, 
  t : int, gamma : int) -> bool:
  k = len(X)
  assert len(Y) == k
  assert len(A) == k + 1
  assert len(r) == k + 1

  U = mod_exp(D, t, p)
  W = mod_exp(C, t, p)
  X_hat = [(X[i] * mod_exp(U, -1, p)) % p for i in range(k)]
  Y_hat = [(Y[i] * mod_exp(W, -1, p)) % p for i in range(k)]

  # Step 2: Verify equations for A and r
  ret = True

  # Check first equation: Ŷ_1^{r_0} = A_0 * X̃_1^{-γ}
  lhs = mod_exp(Y_hat[0], r[0], p)
  rhs = (A[0] * mod_exp(X_hat[0], -gamma, p)) % p
  ret = ret & (lhs == rhs)

  # Check middle equations: X̃_i^{r_{i-1}} * Ŷ_i^{r_i} = A_i
  for i in range(1, k):
    lhs = (mod_exp(X_hat[i], r[i-1], p) * mod_exp(Y_hat[i], r[i], p)) % p
    ret = ret & (lhs == A[i])

  # Check last equation: X̃_k^{r_{k-1}} = A_k * Ŷ_k^{(-1)^k * γ}
  lhs = mod_exp(g, r[-1], p)
  term = (B * mod_exp(T, lam, p) * mod_exp(g, -s, p)) % p
  rhs = (A[-1] * mod_exp(term, ((-1)**k) * gamma, p)) % p
  ret = ret & (lhs == rhs)

  return ret


# simple_k_shuffle_proof_II(p : int, q : int, g : int,
 # X : List[int], Y : List[int], x : List[int], y : List[int],
 # c : int, d : int, beta : int, tau : int, lam : int, t : int, 
 # gamma : int)
# Testing code
p, q, g = generate_parameters(100)
N = 100
c, d = (getRandomRange(1, q) for _ in range(2))
x = [getRandomRange(1, q) for _ in range(N)]
permutation = [i for i in range(N)]
random.shuffle(permutation)
# Y_i^d = X_{π(i)}^c
# g^{y_i * d} = g^{x_{π(i)}^c}
# g^y_i = g^{c * x_{π(i)} * d^{-1}}
# y_i = (c * x_{π(i)} * d^{-1}) mod q
y = [(c * x[permutation[i]] * mod_exp(d, -1, q)) % q for i in range(N)]
X = [pow(g, x[i], p) for i in range(N)]
Y = [pow(g, y[i], p) for i in range(N)]
beta, tau, lam = (getRandomRange(1, q) for _ in range(3))
t = getRandomRange(1, q)
gamma = getRandomRange(1, q)
C, D, B, T, s, A, r = simple_k_shuffle_proof_II(p, q, g,
  X, Y, x, y, c, d, beta, tau, lam, t, gamma)
print(simple_k_shuffle_verify_II(p,
  X, Y, B, T, s, C, D, A, r, lam, t, gamma))
# End of k-shuffle protocol II    