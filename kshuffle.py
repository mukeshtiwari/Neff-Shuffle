from Crypto.Util.number import getPrime, getRandomRange, isPrime
from typing import List, Tuple
from util import mod_exp, generate_parameters
from ilmpp import ilmpp_proof, ilmpp_verification
import random

# Beginning of simple k-shuffle protocol

# Commitment function
def commitment(p : int, g : int, c : int) -> int : 
  C = mod_exp(g, c, p)  # C = g^c
  return C


# Computes X_hat = X * U^-1 mod p 
def compute_hat(p : int, X : List[int], U : int) -> List[int]:
  k = len(X)
  X_hat = [(X[i] * mod_exp(U, -1, p)) % p for i in range(k)]
  return X_hat


# Two sequences of k elements of Zp, X1, . . . , Xk , and Y1, . . . , Yk are publicly known. The
# prover, P, also knows xi = log_{g} Xi and yi = log_{g} Yi, but these are unknown to the verifier, V. 
# In addition, constants c and d in Zq are known only to P, but commitments C = g^c
# and D = g^d are made public. P is required to convince V that there is some permutation, π ∈ Σk , with the property
# that Y_{i}^d = X_{π(i)}^c for all i ∈ {1, . . . , k}.


def simple_k_shuffle_proof(p : int, q : int, g : int, X : List[int], Y : List[int], 
  x : List [int], y : List [int], c : int, d : int, t : int, gamma : int) -> Tuple[List[int], List[int]] : 
  k = len(X)
  assert len(Y) == k
  assert len(x) == k
  assert len(y) == k

  # 1 # V generates a random t ∈ Zq and gives it to P as a challenge.
  # In practice, we should use Fiat-Shamir heuristic to generate the challenge
  # and here we have passed it as a parameter
  # t = getRandomRange(1, q)

  C = commitment(p, g, c)  # C = g^c
  D = commitment(p, g, d)  # D = g^d

  # 2 # P computes U = D^t, W = C^t, X_hat = X * U^-1, Y_hat = Y * W^-1
  U = commitment(p, D, t)  # U = D^t mod p 
  W = commitment(p, C, t) # W = C^t mod p
  X_hat = compute_hat(p, X, U) # X_hat = X * U^-1 mod p
  Y_hat = compute_hat(p, Y, W) # Y_hat = Y * W^-1 mod p

  # 3 P and V execute the SILPP for the two length 2k vectors
  Xret = X_hat + [C] * k  # φ
  Yret = Y_hat + [D] * k  # ψ
  # adjust the x and y values according to X_hat and Y_hat
  # X_hat_i = g^{x_i - d * t} and Y_hat_i = g^{y_i - c * t} 
  x_hat_logs = [(xi - d * t) % q for xi in x]
  y_hat_logs = [(yi - c * t) % q for yi in y]
  xret = x_hat_logs + [c] * k
  yret = y_hat_logs + [d] * k
  A, r = ilmpp_proof(p, q, Xret, Yret, xret, yret, gamma)

  return C, D, A, r 


def simple_k_shuffle_verification(p : int, X : List[int], Y : List[int], 
  A : List[int], r : List[int], C : int, D : int, t : int, gamma : int) -> bool:
  k = len(X)
  assert len(Y) == k
  assert len(A) == (2 * k)
  assert len(r) == (2 * k - 1)
  U = commitment(p, D, t)  # U = D^t mod p 
  W = commitment(p, C, t) # W = C^t mod p
  X_hat = compute_hat(p, X, U) # X_hat = X * U^-1 mod p
  Y_hat = compute_hat(p, Y, W) # Y_hat = Y * W^-1 mod p
  Xret = X_hat + [C] * k  # φ
  Yret = Y_hat + [D] * k  # ψ
  return ilmpp_verification(p, Xret, Yret, A, r, gamma) 

#Testing code
def main():
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
  t = getRandomRange(1, q)
  gamma = getRandomRange(1, q)
  C, D, A, r = simple_k_shuffle_proof(p, q, g, X, Y, x, y, c, d, t, gamma)
  print(simple_k_shuffle_verification(p, X, Y, A, r, C, D, t, gamma))

if __name__ == "__main__":
  main()
# End of simple k-shuffle protocol
