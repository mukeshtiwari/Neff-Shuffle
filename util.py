from Crypto.Util.number import getPrime, getRandomRange, isPrime


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