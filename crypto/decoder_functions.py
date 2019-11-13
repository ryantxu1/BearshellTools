import requests
import json
import string
import binascii
import gmpy
import gmpy2
from math import gcd
from Crypto.Util.number import *
import owiener
import os
os.environ['PWNLIB_NOTERM'] = 'True'  # Configuration patch to allow pwntools to be run inside of an IDE
from pwn import *



def ascii2hex(text):
    try:
        text = text.encode()
        return binascii.b2a_hex(text).decode()
    except ValueError:
        return "INVALID INPUT"


def hex2ascii(text):
    try:
        return binascii.a2b_hex(text).decode()
    except ValueError:
        return "INVALID INPUT"


def hex2bin(text):
    try:
        return bin(int(text, 16))[2:]
    except ValueError:
        return "INVALID INPUT"


def bin2dec(text):
    try:
        return int(text, 2)
    except ValueError:
        return "INVALID INPUT"


def bin2hex(text):
    text = text.replace(' ', '')
    try:
        return hex(int(text, 2)).replace('0x', '')
    except ValueError:
        return "INVALID INPUT"


def dec2bin(text):
    try:
        return "{0:b}".format(int(text))
    except ValueError:
        return "INVALID INPUT"


def dec2hex(text):
    try:
        return hex(int(text)).replace('0x', '')
    except ValueError:
        return "INVALID INPUT"


# Handles all kinds of Caesar/ROT ciphers. Accepts two parameters: {str: text}, {bool: space}. 'text' is ciphertext,
# 'space' is boolean denoting whether space characters should be rotated or not (True if yes)
def caesar_cipher_decoder2(text, space):
    plaintext = []
    for key in range(94):
        result = ""
        # traverse text
        for i in range(len(text)):
            char = text[i]

            if not space and char == " ":
                result += char

            else:
                char_ascii = ord(char)
                char_ascii += key
                if char_ascii > 126:
                    char_ascii = char_ascii - 94

                result += chr(char_ascii)

        plaintext.append('key:' + str(94-key) + " - " + result)

    plaintext.reverse()
    return plaintext


def vigenere_cipher_decoder(text, key):
    orig_text = []
    for i in range(len(text)):
        x = (ord(text[i]) -
             ord(key[i]) + 26) % 26
        x += ord('A')
        orig_text.append(chr(x))
    return "" . join(orig_text)


# makes a call to quipqiup.com for frequency analysis
def decode_substitute(cipher, time=4, spaces=True):
    solutions = []

    url = "https://6n9n93nlr5.execute-api.us-east-1.amazonaws.com/prod/solve"
    clues = ''
    data = {
        'ciphertext': cipher,
        'clues': clues,
        'solve-spaces': spaces,
        'time': time
    }
    headers = {
        'Content-type': 'application/x-www-form-urlencoded',
    }

    ret = requests.post(url, data=json.dumps(data), headers=headers).text
    print(ret)
    ret_json = json.loads(ret)
    for solution in ret_json["solutions"]:
        solutions.append(solution["plaintext"])

    return solutions


def ECB_byte_at_a_time(server, port):
    r = remote(server, port)
    plaintext = ""

    # find number of blocks
    r.sendline('')
    whole_text = r.recvuntil("\n")
    block = len(whole_text)/16

    for k in range(int(block)):
        b = ""
        for i in range(1, 17):
            string_sent = "a" * (16 - i)

            r.recv()
            r.sendline(string_sent)
            g1 = r.recvuntil("\n")[16:-1]
            g1 = g1[:32 + k * 32]
            print("String sent: ", string_sent)
            for j in range(256):
                r.recv()
                r.sendline(string_sent + plaintext + b + chr(j))
                g2 = r.recvuntil("\n")[16:-1]
                g2 = g2[:32 + k * 32]
                if g1 == g2 and chr(j) in string.printable and j != 10 and j != 0:
                    print(chr(j), j)
                    b += chr(j)
                    break
        plaintext += b
        print(plaintext)


# direct square root vulnerability (low public exponent attack), possible when e is very small and n is large
def RSA_direct_square_root(c, e):
    m = gmpy.root(c, e)[0]
    return str(long_to_bytes(m)).replace('b', '').replace('\'', '')


# If N is not too large, use "yafu" tool to find p and q. Can also use https://www.alpertron.com.ar/ECM.HTM
def RSA_solver(p, q, e, c):
    n = p * q
    phi = (p - 1) * (q - 1)
    d = gmpy.invert(e, phi)
    m = pow(c, d, n)

    return str(long_to_bytes(m)).replace('b', '').replace('\'', '')


# RSA Wiener attack. Works when d < 1/3*n^(1/4), n=pq, q<p<2q
def RSA_wiener(e, n, c):
    d = owiener.attack(e, n)
    m = pow(c, d, n)
    return str(long_to_bytes(m)).replace('b', '').replace('\'', '')


# Given phi, applicable when multiple primes exist, use https://www.alpertron.com.ar/ECM.HTM
def RSA_multi_prime(phi, e, n, c):
    d = gmpy.invert(e, phi)
    m = pow(c, d, n)

    return str(long_to_bytes(m)).replace('b', '').replace('\'', '')


# e1 --> Public Key exponent used to encrypt message m and get ciphertext c1
# e2 --> Public Key exponent used to encrypt message m and get ciphertext c2
# n --> Modulus
# The following attack works only when m^{GCD(e1, e2)} < n
def RSA_common_modulus(e1, e2, n, c1, c2):
    def egcd(a, b):
        if a == 0:
            return b, 0, 1
        else:
            g, y, x = egcd(b % a, a)
            return g, x - (b // a) * y, y

    # Calculates a^{b} mod n when b is negative
    def neg_pow(a, b, n):
        assert b < 0
        assert GCD(a, n) == 1
        res = int(gmpy2.invert(a, n))
        res = pow(res, b * (-1), n)
        return res

    g, a, b = egcd(e1, e2)

    if a < 0:
        c1 = neg_pow(c1, a, n)
    else:
        c1 = pow(c1, a, n)
    if b < 0:
        c2 = neg_pow(c2, b, n)
    else:
        c2 = pow(c2, b, n)
    ct = c1*c2 % n
    m = int(gmpy2.iroot(ct, g)[0])
    return long_to_bytes(m)


# Message is sent to >2 people with same public key exponent e
def RSA_Hastad_unpadded(ct_list, mod_list, e):
    def crt(list_a, list_m):
        """
        Reference: https://crypto.stanford.edu/pbc/notes/numbertheory/crt.html
        Returns the output after computing Chinese Remainder Theorem on
        x = a_1 mod m_1
        x = a_2 mod m_2
        ...
        x = a_n mod m_n
        input parameter list_a = [a_1, a_2, ..., a_n]
        input parameter list_m = [m_1, m_2, ..., m_n]
        Returns -1 if the operation is unsuccessful due to some exceptions
        """
        try:
            assert len(list_a) == len(list_m)
        except:
            print("[+] Length of list_a should be equal to length of list_m")
            return -1
        for i in range(len(list_m)):
            for j in range(len(list_m)):
                if GCD(list_m[i], list_m[j]) != 1 and i != j:
                    print("[+] Moduli should be pairwise co-prime")
                    return -1
        M = 1
        for i in list_m:
            M *= i
        list_b = [M / i for i in list_m]
        assert len(list_b) == len(list_m)
        try:
            list_b_inv = [int(gmpy2.invert(list_b[i], list_m[i])) for i in range(len(list_m))]
        except:
            print("[+] Encountered an unusual error while calculating inverse using gmpy2.invert()")
            return -1
        x = 0
        for i in range(len(list_m)):
            x += list_a[i] * list_b[i] * list_b_inv[i]
        return x % M

    m_expo = crt(ct_list, mod_list)
    if m_expo != -1:
        eth_root = gmpy2.iroot(m_expo, e)
        if eth_root[1] == False:
            print("[+] Cannot calculate e'th root!")
            return -1
        elif eth_root[1] == True:
            return long_to_bytes(eth_root)
    else:
        print("[+] Cannot calculate CRT")
        return -1
