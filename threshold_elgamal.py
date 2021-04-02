# Threshold ElGamal Encryption Implementation
#
# The following code assumes that PyCryptodome has been installed using
#   pip install pycryptodomex
# Documentation for PyCryptodome
#   https://pycryptodome.readthedocs.io/en/latest/

from Cryptodome.Random import random
from Cryptodome.Util import number
import numpy as np
import math as m1
import hashlib
from decimal import Decimal
from numpy.compat import long
from fractions import Fraction

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

# Modular exponentiation using square-and-multiply method
#
# a: base
# x: exponent
# p: modulus
#
# returns (a^x) mod p computed using O(log p) steps
#
def power(a, x, p):
    res = 1
    a = a % p
    if (a == 0):
        return 0
    while (x > 0):
        # Square if exponent is even
        if ((x & 1) == 0):
            a = (a * a) % p
            x = x >> 1
        # Multiply if exponent is odd
        else:
            res = (res * a) % p
            x = x - 1
    return int(res)

# Generation of a random element in the subgroup
#
# q: prime
# p: prime such that q divides p - 1
#
# returns a random element in the subgroup of order q modulo p
#
def random_subgroup(q, p):
    while True:
        h = random.randint(2, p-1)
        g = power(h, (p-1)//q, p)
        if (g != 1):
            break
    return g


# Generation of system parameters
#
# qbits: bit length of q, the subgroup of prime order q
# pbits: bit length of p, the modulus
#
# returns (g, q, p), where g is a generator of the subgroup of order q mod p
#
def get_params(qbits, pbits):
    while True:
        while True:
            q = random.getrandbits(qbits)
            if (number.isPrime(q)):
                break
        m = random.getrandbits(pbits - qbits - 1)
        p = m * q + 1
        if (number.isPrime(p)):
            break
    g = random_subgroup(q, p)
    return (g, q, p)


# Key generation
# 
# g: group generator
# p: modulus
# q: group order
#
# returns (y, x, g_hat), where y is the public key, x is the secret/private key and g_hat is a group element
#
def generate_keys(g, q, p):
    x = random.randint(2,q-1)
    y = power(g, x, p)
    g_hat = random_subgroup(q, p)
    return (y, x, g_hat)


# Encryption
#
# g, g_hat: group generators
# q: group order
# p: modulus
# y: public key
# m: plaintext message
#
# returns ElGamal-encryption of m under public key y
#
def elgamal_encrypt(g, g_hat, q, p, y, m):
    r = random.randint(2, q - 1)
    s = random.randint(2, q - 1)
    rG = (power(y, r, p))

    h = hashlib.sha256(str(rG).encode()).hexdigest()
    m = str(m).encode('utf-8').hex()
    c = (hex(long(h, 16) ^ long(m, 16)))[2:]
    u = power(g, r, p)
    w = power(g, s, p)
    u_hat = power(g_hat, r, p)
    w_hat = power(g_hat, s, p)
    e = hash_2(c, u, w, w_hat, u_hat, q)
    f = (s + r*e) % q
    return (c, u, u_hat, e, f)

# Implements H2 in the paper
#
# hx: hex string
# g1: group element 
# g2: group element 
# g3: group element 
# g4: group element 
# q:  group order
#
# returns integer in Zq
#
def hash_2(hx, g1, g2, g3, g4, q):
    return int(hashlib.sha256(str("{}{}{}{}{}".format(hx[2:], g1, g2, g3, g4)).encode('utf-8')).hexdigest(), 16) % q

# Implements H4 in the paper
#
# g1: group element
# g2: group element
# g3: group element
# q:  group order
#
# returns integer in Zq
#
def hash_4(g1, g2, g3, q):
    return int(hashlib.sha256(str("{}{}{}".format(g1, g2, g3)).encode('utf-8')).hexdigest(), 16) % q

# Get Lagrange coefficient
#
# indices: set of indeces 
# i: index of coefficient
# q: group order
#
# returns result as integer in Zq
#
def lagrange_coeff(indices, i, q):
    prod = 1
    for k in range(len(indices)):
        j = indices[k]

        if i != j:
            prod *= (j% q) * number.inverse(j-i, q)

    return prod

# Gets value of polynomial with coefficients a at point x
#
# x: point to evaluate
# a: array of coefficients
# q: group order
#
# returns value at point x in Zq
#
def eval_pol(x, a, q):
    val = 0
    for i in range(len(a)):
        val += (x**(len(a) - i - 1)) * (a[i])

    return val % q

# Share secret key using Shamir Secret Sharing
#
# x: private key
# k: number of shares needed for reconstruction
# n: number of shares in total
# q: group order
# g: group generator
#
# returns list of key shares in Zq and a verification key
#
def share_key(x, k, n, q, g):
    f = np.array(x)
    for i in range(k - 1):
        f = np.append(f, random.randint(2, q - 1))

    f = [4, 3, x]
    shares = []
    verificationKey = []
    for j in range(1, n+1):
        xi = eval_pol(j, f, q)
        hi = power(g, xi, p)
        verificationKey.append(hi)
        shares.append((j, xi))
    return shares, verificationKey

# Partially decrypt ciphertext using key share
# 
# encryption: encrypted message
# s: key share
# g: group generator
# p: modulus
# q: group order
#
# returns partial decryption result
#
def get_partial(encryption, s, g, p, q):
    c, u, u_hat, e, f = encryption
    w = (power(g, f, p) * number.inverse(power(u, e, p), p)) % p
    w_hat = (power(g_hat, f, p) * number.inverse(power(u_hat, e, p), p)) % p

    if(e != hash_2(c, u, w, w_hat, u_hat, q)):
        return (s[0], "?")

    si = random.randint(2, q-1)
    ui = power(u, s[1], p)
    ui_hat = power(u, si, p)
    hi_hat = power(g, si, p)
    ei = hash_4(ui, ui_hat, hi_hat, q)
    fi = (si + (int(s[1])*ei)) % q

    return (s[0], ui, ei, fi) 


# Verfify decryption share
#
# share: decryption share
# verificationKey: verification Key
# encryption: encrypted message
# q: group order
# 
# returns boolean indicating whether given decryption share is valid
#
def verify_share(share, verificationKey, encryption, q):
    c, u, u_hat, e, f = encryption
    i, ui, ei, fi = share
    hi = verificationKey[i - 1]

    if(ui == "?"):
        return False

    ui_hat = (power(u, fi, p) * number.inverse(power(ui, ei, p), p)) % p
    hi_hat = (power(g, fi, p) * number.inverse(power(hi, ei, p), p)) % p

    return ei == hash_4(ui, ui_hat, hi_hat, q)

# Combine partial results to get encrypted message
#
# encryption: encrypted message
# verificationKey: key to verify shares
# shares: partial results
# p: modulus
# q: group order
#
# returns decrypted message
#
def combine_shares(encryption, verificationKey, shares, p, q):
    rG = 1
    c, u, u_hat, e, f = encryption
    for i in range(len(shares)):
        if(shares[i][1] == "?"):
            return "?"

        id, ui, ei, fi = shares[i]

        if(verify_share(shares[i], verificationKey, encryption, q) == False):
            print(bcolors.FAIL + "Share {} invalid".format(shares[i]) + bcolors.ENDC)
            return "?"

        l = lagrange_coeff([sh[0] for sh in shares], shares[i][0], q)
        ui = power(ui, l, p)
        rG *=  ui

    rG = int(rG)
    rG %= p

    h = hashlib.sha256(str(rG).encode()).hexdigest()
    m = (hex(long(h, 16) ^ long(c, 16)))[2:]

    return bytearray.fromhex(m).decode()

# Combine key shares to get private key
#
# shares: list of key shares
# q: order of group
#
# returns private key as integer in Zq
#
def combine_key_shares(shares, q):
    key = 0
    for i in range(len(shares)):
        xj, yj = shares[i]
        prod = lagrange_coeff([sh[0] for sh in shares], xj, q) * yj
        key += prod
 
    return int(key) % q


# threshold parameters 
k = 3 # threshold
n = 5 # number of key shares

print(bcolors.OKCYAN + "[*] Generating ElGamal key pair..." + bcolors.ENDC)
#(g, q, p) = get_params(256, 2048)  # more secure version (but slower)
(g, q, p) = get_params(50, 60)      # for testing purposes (insecure but faster)
(y, x, g_hat) = generate_keys(g, q, p)

print(bcolors.WARNING + "[+] Private Key: {} ".format(x))
print(bcolors.WARNING + "[+] Public Key: {} ".format(y))

# generate key shares and verification key
keys, verificationKey = share_key(x, k, n, q, g)
print("[+] Key shares: {} \n".format(keys) + bcolors.ENDC)

# select k random keys out of key shares
selected_keys = random.sample(keys, k)

m = input(bcolors.OKCYAN + "[*] Enter message: ")

# clip message if longer than 64 characters
if(len(m) > 64):
    m = m[:64]

# encrypt message
encryption = elgamal_encrypt(g, g_hat, q, p, y, m)
print(bcolors.WARNING + "[+] Encrypted message: {}".format(encryption))

# get partial results
d = [get_partial(encryption, key, g, p, q) for key in selected_keys]
print("[+] Partial results: {} ".format(d))

# reconstruct secret to check whether shamir share works
print("[+] Reconstructed secret: {}" .format(combine_key_shares(selected_keys, q)))

# reconstruct message out of partial results
message = combine_shares(encryption, verificationKey, d, p, q)
print(bcolors.OKGREEN + "[+] Decrypted message: {}".format(message) + bcolors.ENDC)