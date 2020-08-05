#!/usr/bin/env python
# coding: utf-8

import numpy as np
import os
import sys
import secrets
import scipy as sp
import math
import time
from sympy.discrete import convolutions
from sympy.polys import *
from sympy import GF
from scipy.signal import fftconvolve
from sympy import pprint
from sympy.abc import x,y,z
# from __future__ import print_function, division
from sympy.core.compatibility import range
from sympy.ntheory import nextprime
from Crypto.Util import number
from Crypto.Hash import SHA256




import pickle




# information about the prime number
# primeNum .bit_length()
# "{0:b}".format(primeNum)
# isprime(primeNum)
# number_of_ones(primeNum)
# primeNum



# output hamming weight of the number
def number_of_ones(n):
    c = 0
    while n:
        c += 1
        n &= n - 1
    return c


# output a prime number that fits the requirement
def find_prime():
    n_length = 26
    primeNum = number.getPrime(n_length)
    while True:
    #     print(primeNum)
    #     print(primeNum.bit_length())
        if primeNum % 256 == 1 and number_of_ones(primeNum) <= 3:
            break
        primeNum = number.getPrime(n_length)


# general parameters
N = 7
M = 15
# degree of the polynomial in the matrix G' (use 128)
DEGREE = 128
# q: random prime; around size 2^26 bits, pq = 1 mod 256
Q = 33564673
# r: vector of polynomials of deg (d-1); coeffcient is random from [1, 0, -1]
# pk_list = G * r, deg (d-1), coeff mod q; all mod to the x^d + 1


# useful global varaibles to avoid repeat computation
one_poly = [1] * DEGREE
zero_poly = [0] * DEGREE
one_poly = Poly(one_poly, x, modulus = Q, symmetric = True)
zero_poly = Poly(zero_poly, x, modulus = Q, symmetric = True)

# x**d + 1
modulus_poly = [0] * (DEGREE + 1)
modulus_poly[0] = 1
modulus_poly[DEGREE] = 1
modulus_poly = Poly(modulus_poly, x, modulus = Q, symmetric = True)

# for polynomial multiplication, either use fftconvolve(m1, m2) or Poly1 * Poly2


# return a random polynomial with degree d - 1 and coefficient mod Q
def random_poly(d):
    vector = [None] * d
    for i in range (d):
        vector[i] = secrets.randbelow(Q)
    return Poly(vector, x, modulus = Q, symmetric = True)


# return a random polynomial with degree d - 1 and coefficient 0, 1 or -1
def random_special_poly(d):
    choice_list = [0, 1, -1]
    vector = [None] * d
    for i in range (d):
        vector[i] = secrets.choice(choice_list)
    return Poly(vector, x, modulus = Q, symmetric = True)


# generate polynomial in S with degree d - 1 and coefficient mod md^2
def generate_S(d):
    vector = [None] * d
    for i in range (d):
        num = secrets.randbelow(M * d**2 * 2)
        num = num - M * d**2
        vector[i] = num
    return Poly(vector, x, modulus = Q)



# return the vector S with M + 1 polynomials
def random_special_S(d):
    column = []
    for i in range (M):
        column.append(generate_S(d))
#     append 0 polynomial at end
    column.append(zero_poly)
    np_column = np.asarray(column)
    return (np.transpose(np_column))


# return the vector with all coefficient 1, 0 or -1 with M + 1 
def random_special_column(d):
    column = []
    for i in range (M):
        column.append(random_special_poly(d))
#     append 0 polynomial at end
    column.append(zero_poly)
    np_column = np.asarray(column)
    return (np.transpose(np_column))


# input: one_x: one specific x(a polynomial); one_pk: one public key, a vector of polynomials
def x_pk_mul(one_x, one_pk):
    result = [None] * len(one_pk)
    for i in range (len(one_pk)):
#         call ntt
        product = convolutions.convolution_ntt(one_x.all_coeffs(), one_pk[i].all_coeffs(), prime = 16389* 2**11 + 1)
        result[i] = Poly(product, x, modulus = Q, symmetric = True)
    return np.asarray(result)


# transform a number to its ternary form
def ternary(n):
    if n == 0:
        return '0'
    nums = []
    while n:
        n, r = divmod(n, 3)
        nums.append(str(r))
    return ''.join(reversed(nums))


# input: a ternary string; the number of bits should be larger than the highest degree
# output: a polynomial with each coefficient between 0, 1, -1
# ternary 2 becomes -1 in our case
def ternary_poly(ter_str, degree):
    coef = []
    for i in range (degree):
        current_num = int(ter_str[i])
        if current_num == 2:
            coef.append(-1)
        else:
            coef.append(current_num )
    return Poly(coef, x, modulus = 3, symmetric = True)


# check if z coefficients are in range 
# return 0 if fail, 1 if success
def z_check(z):
#     start_time = time.time()
    for i in range (len(z)):
        this_poly = z[i]
        this_coef = this_poly.all_coeffs()
        for coef in this_coef:
            c = int(coef)
            c = abs(coef)
            if c > M * DEGREE**2 - DEGREE:
#             print(coef)
#             if coef > 0:
#                 print('z check failed')
                return 0
    return 1


# doing z_check on a specific row
def z_check_row(z):
#     start_time = time.time()
    this_coef = z.all_coeffs()
    for coef in this_coef:
        c = int(coef)
        c = abs(coef)
        if c > M * DEGREE**2 - DEGREE:
#             print(coef)
#             if coef > 0:
#                 print('z check failed')
            return 0
    return 1


# transform the x corresponded to the secret key to have coefficient 0, 1 or -1
def find_my_x(p):
    coef = []
    my_coef = p.all_coeffs()
    length = len(my_coef)
    difference = DEGREE - length
    for i in range (length):
        current_num = int(my_coef[length - i - 1]) % 3
        if current_num == 2:
            coef.append(-1)
        else:
            coef.append(current_num)
    for i in range (difference):
        coef.append(0)
    list.reverse(coef)
    return Poly(coef, x, modulus = 3, symmetric = True)


# using ntt and matrix multiplication (involving matrix G)
def G_mul(g, s):
    result = []
    for i in range (N):
        result.append(Poly([0], x, modulus = Q, symmetric = True))
    for i in range(len(g)): 
        for k in range(len(s)): 
            product = convolutions.convolution_ntt(g[i][k].all_coeffs(), s[k].all_coeffs(), prime = 16389* 2**11 + 1)
            result[i] = result[i] + Poly(product, x, modulus = Q, symmetric = True)
    return np.asarray(result)


# scheme in the paper
def RSetup(m, n, degree):
    entire_list = []
    for i in range (n):
        this_row = []
        for j in range (m + 1):
            if j == i:
                this_row.append(one_poly)
            elif j < N:
                this_row.append(zero_poly)
            else:
                this_row.append(random_poly(degree))
        entire_list.append(this_row)
    G = np.asarray(entire_list)
    return G


# Generate one pairs of keys
def RkeyGen(m, n, degree, G):
#     multiplying two matrices
    sk = random_special_column(degree)
    pk = G_mul(G, sk)
    
#     reducing by mod x**d - 1
    for ii in range (len(pk)):
        foo, pk[ii] = div(pk[ii], modulus_poly)
    return pk, sk


# In[1085]:


# scheme in the paper
def RSign(message, pk_list, position, sk, G, time_restart):
    s = random_special_S(DEGREE)
    
    row = [None] * key_list_size
    for i in range (key_list_size):
        if i == position:
            continue
        row[i] = random_special_poly(DEGREE)
    x_list = np.asarray(row)
        
    t = G_mul(G, s)
    for ii in range (len(t)):
        foo, t[ii] = div(t[ii], modulus_poly)

    summation = 0
    for i in range (len(x_list)):
        if i == position:
            continue
        summation = summation + x_pk_mul(x_list[i], pk_list[i])
    
    t = t + summation

#     reduction
    for i in range (len(t)):
        foo, t[i] = div(t[i], modulus_poly)
        t[i] = Poly(t[i].all_coeffs(), x, modulus = Q, symmetric = True)
        
    t_hash = []
    for i in range (len(t)):
        t_hash.append(t[i].all_coeffs())
    t_hash = np.asarray(t_hash)
    t_hash = str(t_hash).encode()
    
#     hashing
#     it seems that simply hashing the list t is not going to work, try to create a list of coeffs
    sha = SHA256.new()
    sha.update(message.encode())
    sha.update(pk_list)
    sha.update(t_hash)
    hashed_product = int(sha.hexdigest(), 16)
    ternaray_string = ternary(hashed_product)
    x_poly = ternary_poly(ternaray_string, DEGREE)
    
#     subtracting
    my_x = x_poly
    for ii in range (len(x_list)):
        if ii == position:
            continue
        this_poly = Poly(x_list[ii].all_coeffs(), x, modulus = 3, symmetric = True)
        my_x = my_x - this_poly
    my_x = find_my_x(my_x)
    my_x = Poly(my_x.all_coeffs(), x, modulus = Q, symmetric = True)
    x_list[position] = my_x
        
    z = [None] * (M + 1)
    z = np.asarray(z)
    for i in range (len(z)):
        x_coef = convolutions.convolution_ntt(my_x.all_coeffs(), sk[i].all_coeffs(), prime = 16389* 2**11 + 1)
        z[i] = Poly(x_coef, x, modulus = Q, symmetric = True) - s[i]
        foo, z[i] = div(z[i], modulus_poly)
        z[i] = Poly(z[i].all_coeffs(), x, modulus = Q, symmetric = True)
        if z_check_row(z[i]) == 0:
            time_restart[0] += 1
            return RSign(message, pk_list, position, sk, G, time_restart)
        
    return (z, x_list)


def RVerify(message, pk_list, position, sk, G, sigma):
    z = sigma[0]
    x_list = sigma[1]

    if z_check(z) == 0:
        print('z check failed in verify stage')
        return 0
    
    t = x_pk_mul(x_list[0], pk_list[0])
    for i in range (key_list_size - 1):
        t = t + x_pk_mul(x_list[i + 1], pk_list[i + 1])
    t = t - G_mul(G, z)

    
#     reduce t
    for i in range (len(t)):
        foo, t[i] = div(t[i], modulus_poly)
        t[i] = Poly(t[i].all_coeffs(), x, modulus = Q, symmetric = True)
    
    t_hash = []
    for i in range (len(t)):
        t_hash.append(t[i].all_coeffs())
    t_hash = np.asarray(t_hash)
    t_hash = str(t_hash).encode()
    
    sha = SHA256.new()
    sha.update(message.encode())
    sha.update(pk_list)
    sha.update(t_hash)
    hashed_product = int(sha.hexdigest(), 16)
    ternaray_string = ternary(hashed_product)
    x_poly = ternary_poly(ternaray_string, DEGREE)
    
    sum_x = 0
    for i in range (len(x_list)):
        sum_x = sum_x + x_list[i]
    sum_x = find_my_x(sum_x)
    
    if sum_x != x_poly:
        print('R VERIFY FAILED')
        return 0
    return 1



restart_counter_long = []
for i in range (10):
    restart_counter_long.append([])


all_sign_time_long = []
all_verify_time_long = []
all_total_time_long = []


# testing 
for p_2 in range (8):
    key_list_size = 2**(p_2 + 1)
    G = RSetup(M, N, DEGREE)
    message = 'the'
    pk_list = []
    sk_list = []
    for i in range (key_list_size):
        pk, sk = RkeyGen(M, N, DEGREE, G)
        pk_list.append(pk)
        sk_list.append(sk)
    pk_list = np.asarray(pk_list)
    sk_list = np.asarray(sk_list)
    
    sign_time = []
    verify_time = []
    total_time = []
    
    for trails in range (100):
        times_restart = [0]
        position = secrets.randbelow(key_list_size)
        start_time = time.time()
        sigma = RSign(message, pk_list, position, sk_list[position], G, times_restart)
        sign_time.append(time.time() - start_time)
        middle_time = time.time()
        if RVerify(message, pk_list, position, sk_list[position], G, sigma) == 0:
            break
        verify_time.append(time.time() - middle_time)
        total_time.append(time.time() - start_time)
        restart_counter_long[p_2].append(times_restart[0])
    all_sign_time_long.append(sign_time)
    all_verify_time_long.append(verify_time)
    all_total_time_long.append(total_time)



print(all_sign_time)
print(all_verify_time)
print(all_total_time)
print(restart_counter)


# writing to file
with open("LWE Ring Signature Time Analysis Long.txt", "w") as text_file:
    text_file.write("N Size\t")
    text_file.write("2 Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("4 Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("8 Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("16 Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("32 Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("64 Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("128 Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("256 Sign\tVerify\tTotal\tTimes of Restart\n")
    for i in range (100):
        text_file.write("%d\t" % (i))
        for j in range (8):
            text_file.write("%s\t%s\t%s\t%s\t" % (all_sign_time_long[j][i], 
                                                  all_verify_time_long[j][i], all_total_time_long[j][i], 
                                                  restart_counter_long[j][i]))
        text_file.write("\n")



# another testing 
for p_2 in range (2):
    print(p_2)
    key_list_size = 2**(p_2 + 8)
    G = RSetup(M, N, DEGREE)
    message = 'the'
    pk_list = []
    sk_list = []
    for i in range (key_list_size):
        pk, sk = RkeyGen(M, N, DEGREE, G)
        pk_list.append(pk)
        sk_list.append(sk)
    pk_list = np.asarray(pk_list)
    sk_list = np.asarray(sk_list)
    
    sign_time = []
    verify_time = []
    total_time = []
    
    for trails in range (10):
        times_restart = [0]
        position = secrets.randbelow(key_list_size)
        start_time = time.time()
        sigma = RSign(message, pk_list, position, sk_list[position], G, times_restart)
        sign_time.append(time.time() - start_time)
        middle_time = time.time()
        if RVerify(message, pk_list, position, sk_list[position], G, sigma) == 0:
            break
        verify_time.append(time.time() - middle_time)
        total_time.append(time.time() - start_time)
        restart_counter[p_2].append(times_restart[0])
    all_sign_time.append(sign_time)
    all_verify_time.append(verify_time)
    all_total_time.append(total_time)



# writing to file
with open("LWE Ring Signature Time Analysis Short Modified.txt", "w") as text_file:
    text_file.write("N Size\t")
    text_file.write("2: Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("4: Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("8: Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("16: Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("32: Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("64: Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("128: Sign\tVerify\tTotal\tTimes of Restart\t")
    text_file.write("256: Sign\tVerify\tTotal\tTimes of Restart\n")
    text_file.write("512: Sign\tVerify\tTotal\tTimes of Restart\n")
    text_file.write("1024: Sign\tVerify\tTotal\tTimes of Restart\n")
    for i in range (10):
        text_file.write("%d\t" % (i))
        for j in range (10):
            text_file.write("%s\t%s\t%s\t%s\t" % (all_sign_time[i][j], all_verify_time[i][j], 
                                                  all_total_time[i][j], restart_counter[i][j]))
        text_file.write("\n")
