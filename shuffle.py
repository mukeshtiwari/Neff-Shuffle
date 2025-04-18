from Crypto.Util.number import getPrime, getRandomRange, isPrime
from typing import List, Tuple
import random


# Helper functions
def mod_exp(base, exp, mod):
  return pow(base, exp, mod)


def generate_safe_prime(bits):
  while True:
    q = getPrime(bits)
    p = 2 * q + 1
    if isPrime(p):
      return p, q

# print(generate_safe_prime(64))

# Generate parameters for the ILMPP protocol
def generate_parameters(bits):
  p, q = generate_safe_prime(bits)
  g = 4
  assert pow(g, q, p) == 1
  return p, q, g

# Beginning of ILMPP protocol
# Prover knows: x_i = log_g X_i, y_i = log_g Y_i
def ilmpp_proof(p : int, q : int, X : List[int], Y : List[int], x : List[int], y : List[int], gamma : int) -> Tuple[List[int], List[int]] :
  k = len(X)
  assert len(Y) == k
  assert len(x) == k
  assert len(y) == k
  
  #step 1: generate commitment A1, A2, ... Ak
  theta = [getRandomRange(1, q) for _ in range(k - 1)]
  A = [mod_exp(Y[0], theta[0], p)]
  for i in range(1, k - 1):
      A.append((mod_exp(X[i], theta[i - 1], p) * mod_exp(Y[i], theta[i], p)) % p)
  A.append(mod_exp(X[k - 1], theta[k - 2], p))

  #step 2: get a random challenge from verifier
  # In practice, we should use Fiat-Shamir heuristic to generate the challenge
  # gamma = getRandomRange(1, self.q)

  #step 3: generate response r1, r2, ... rk
  r = [] 
  sign = -gamma 
  acc = 1  
  for i in range(0, k - 1) :
    acc = (acc * (x[i] * mod_exp (y[i], -1, q))) % q
    r.append((theta[i] + sign * acc) % q)
    sign = -sign 
  
  return A, r
  

def ilmpp_verification(p : int,  X : List[int], Y : List[int], A : List[int], r : List[int], gamma) -> bool: 
  k = len(X)
  assert len(Y) == k
  assert len(A) == k
  assert len(r) == (k - 1)

  ret = (pow(Y[0], r[0], p) == ((A[0] * pow(X[0], -gamma, p)) % p))
  for i in range(1, k - 1):
    ret = (ret and (pow(X[i], r[i - 1], p) * pow(Y[i], r[i], p) % p == A[i]))
  ret = (ret and pow(X[k - 1], r[k - 2], p) == (A[k - 1] * pow(Y[k - 1], ((-1) ** (k - 1)) * gamma, p)) % p)

  return ret

    

#Testing code     
p, q, g = generate_parameters(100)
N = 100 
x = [getRandomRange(1, q) for _ in range(N)]
y = [e for e in x]
c, d, e, f, gg, h = (getRandomRange(1, q) for _ in range(6))
x[0] *= c
x[7] *= d
x[2] *= e
x[0] *= f
x[0] *= gg
x[3] *= h
y[1] *= c
y[9] *= d
y[2] *= e
y[5] *= f
y[8] *= gg
y[8] *= h 
X = [pow(g, x[i], p) for i in range(N)]
Y = [pow(g, y[i], p) for i in range(N)]
gamma = getRandomRange(1, q)
A, r = ilmpp_proof(p, q, X, Y, x, y, gamma)
print(ilmpp_verification(p, X, Y, A, r, gamma))

# end of ILMPP protocol


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


def simple_k_shuffle_proof(p : int, X : List[int], Y : List[int], x : List [int], y : List [int], c : int, d : int, t : int, gamma : int) -> Tuple[List[int], List[int]] : 
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

def simple_k_shuffle_verification(p : int, X : List[int], Y : List[int], A : List[int], r : List[int], C : int, D : int, t : int, gamma : int) -> bool:
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
C, D, A, r = simple_k_shuffle_proof(p, X, Y, x, y, c, d, t, gamma)
print(simple_k_shuffle_verification(p, X, Y, A, r, C, D, t, gamma))

# End of simple k-shuffle protocol





