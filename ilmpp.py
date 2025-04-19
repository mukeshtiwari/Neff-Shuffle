from Crypto.Util.number import getPrime, getRandomRange, isPrime
from typing import List, Tuple
from util import mod_exp, generate_parameters


# Beginning of ILMPP protocol
# Prover knows: x_i = log_g X_i, y_i = log_g Y_i
def ilmpp_proof(p : int, q : int, X : List[int], Y : List[int], 
  x : List[int], y : List[int], gamma : int) -> Tuple[List[int], List[int]] :
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
  

def ilmpp_verification(p : int,  X : List[int], Y : List[int], 
  A : List[int], r : List[int], gamma) -> bool: 
  k = len(X)
  assert len(Y) == k
  assert len(A) == k
  assert len(r) == (k - 1)

  ret = (pow(Y[0], r[0], p) == ((A[0] * pow(X[0], -gamma, p)) % p))
  for i in range(1, k - 1):
    ret = (ret and (pow(X[i], r[i - 1], p) * pow(Y[i], r[i], p) % p == A[i]))
  ret = (ret and pow(X[k - 1], r[k - 2], p) == (A[k - 1] * pow(Y[k - 1], ((-1) ** (k - 1)) * gamma, p)) % p)

  return ret

    
def main():
  # Example usage
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

if __name__ == "__main__":
  main()
# end of ILMPP protocol
