'''

 PROGRAM TO BREAK 2 ROUNDS DES ALGORITHM

 Requirements :file "sample_plaintext.txt"  - known plaintext
 			   file "sample_ciphertext.txt"  - known sampletext
			   file "target_ciphertext.txt" - text to be decrypted
 output : target_plaintext.txt -> decrypted plaintext

  The program finds the round keys using the known plain and cipher
  text pair.We also know the last letter of the key is "a", that
  knowledge helps us to reduce the number of possible keys.

  The program find the key but calculating possible values at each step within
  the feistel function using the properties of xor and inverse loop up tables

  The cipher text is decrypted using the round keys
'''

from BitVector import BitVector
import sys
import os
import itertools
from functools import reduce

# all permutation vectors that will be needed
key_permutation_1 = [56,48,40,32,24,16,8,0,57,49,41,33,25,17,
                      9,1,58,50,42,34,26,18,10,2,59,51,43,35,
                     62,54,46,38,30,22,14,6,61,53,45,37,29,21,
                     13,5,60,52,44,36,28,20,12,4,27,19,11,3]

key_permutation_2 = [13,16,10,23,0,4,2,27,14,5,20,9,22,18,11,
                      3,25,7,15,6,26,19,12,1,40,51,30,36,46,
                     54,29,39,50,44,32,47,43,48,38,55,33,52,
                     45,41,49,35,28,31]

shifts_for_round_key_gen = [1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1]

expansion_permutation = [31, 0, 1, 2, 3, 4, 3, 4, 5, 6, 7, 8,
                         7, 8, 9, 10, 11, 12, 11, 12, 13, 14,
                         15, 16, 15, 16, 17, 18, 19, 20, 19,
                         20, 21, 22, 23, 24, 23, 24, 25, 26,
                         27, 28, 27, 28, 29, 30, 31, 0]

p_box_permutation = [15, 6, 19, 20, 28, 11, 27, 16, 0, 14, 22,
                     25, 4, 17, 30, 9, 1, 7, 23, 13, 31, 26,
                     2, 8, 18, 12, 29, 5, 21, 10, 3, 24]

# s-boxes
s_boxes = {i:None for i in range(8)}

s_boxes[0] = [ [14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7],
               [0,15,7,4,14,2,13,1,10,6,12,11,9,5,3,8],
               [4,1,14,8,13,6,2,11,15,12,9,7,3,10,5,0],
               [15,12,8,2,4,9,1,7,5,11,3,14,10,0,6,13] ]

s_boxes[1] = [ [15,1,8,14,6,11,3,4,9,7,2,13,12,0,5,10],
               [3,13,4,7,15,2,8,14,12,0,1,10,6,9,11,5],
               [0,14,7,11,10,4,13,1,5,8,12,6,9,3,2,15],
               [13,8,10,1,3,15,4,2,11,6,7,12,0,5,14,9] ]

s_boxes[2] = [ [10,0,9,14,6,3,15,5,1,13,12,7,11,4,2,8],
               [13,7,0,9,3,4,6,10,2,8,5,14,12,11,15,1],
               [13,6,4,9,8,15,3,0,11,1,2,12,5,10,14,7],
               [1,10,13,0,6,9,8,7,4,15,14,3,11,5,2,12] ]

s_boxes[3] = [ [7,13,14,3,0,6,9,10,1,2,8,5,11,12,4,15],
               [13,8,11,5,6,15,0,3,4,7,2,12,1,10,14,9],
               [10,6,9,0,12,11,7,13,15,1,3,14,5,2,8,4],
               [3,15,0,6,10,1,13,8,9,4,5,11,12,7,2,14] ]

s_boxes[4] = [ [2,12,4,1,7,10,11,6,8,5,3,15,13,0,14,9],
               [14,11,2,12,4,7,13,1,5,0,15,10,3,9,8,6],
               [4,2,1,11,10,13,7,8,15,9,12,5,6,3,0,14],
               [11,8,12,7,1,14,2,13,6,15,0,9,10,4,5,3] ]

s_boxes[5] = [ [12,1,10,15,9,2,6,8,0,13,3,4,14,7,5,11],
               [10,15,4,2,7,12,9,5,6,1,13,14,0,11,3,8],
               [9,14,15,5,2,8,12,3,7,0,4,10,1,13,11,6],
               [4,3,2,12,9,5,15,10,11,14,1,7,6,0,8,13] ]

s_boxes[6] = [ [4,11,2,14,15,0,8,13,3,12,9,7,5,10,6,1],
               [13,0,11,7,4,9,1,10,14,3,5,12,2,15,8,6],
               [1,4,11,13,12,3,7,14,10,15,6,8,0,5,9,2],
               [6,11,13,8,1,4,10,7,9,5,0,15,14,2,3,12] ]

s_boxes[7] = [ [13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7],
               [1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2],
               [7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8],
               [2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11] ]

#inverse sboxes : inverse lookup table for sboxes
is_box = {i:None for i in range(8)}
is_box[ 0 ] = [ [28, 1, 62, 59] , [6, 15, 34, 45] , [8, 11, 44, 39] , [16, 29, 56, 53] ,
                 [2, 7, 32, 41] , [24, 27, 60, 49] , [20, 19, 42, 61] , [30, 5, 54, 47] ,
                 [14, 31, 38, 37] , [26, 25, 52, 43] , [18, 17, 58, 57] , [12, 23, 46, 51] ,
                 [22, 21, 50, 35] , [4, 13, 40, 63] , [0, 9, 36, 55] , [10, 3, 48, 33] ]


is_box[ 1 ] = [ [26, 19, 32, 57] , [2, 21, 46, 39] , [20, 11, 60, 47] , [12, 1, 58, 41] ,
                 [14, 5, 42, 45] , [28, 31, 48, 59] , [8, 25, 54, 51] , [18, 7, 36, 53] ,
                 [4, 13, 50, 35] , [16, 27, 56, 63] , [30, 23, 40, 37] , [10, 29, 38, 49] ,
                 [24, 17, 52, 55] , [22, 3, 44, 33] , [6, 15, 34, 61] , [0, 9, 62, 43] ]



is_box[ 2 ] = [ [2, 5, 46, 39] , [16, 31, 50, 33] , [28, 17, 52, 61] , [10, 9, 44, 55] ,
                 [26, 11, 36, 49] , [14, 21, 56, 59] , [8, 13, 34, 41] , [22, 3, 62, 47] ,
                 [30, 19, 40, 45] , [4, 7, 38, 43] , [0, 15, 58, 35] , [24, 27, 48, 57] ,
                 [20, 25, 54, 63] , [18, 1, 32, 37] , [6, 23, 60, 53] , [12, 29, 42, 51] ]


is_box[ 3 ] = [ [8, 13, 38, 37] , [16, 25, 50, 43] , [18, 21, 58, 61] , [6, 15, 52, 33] ,
                 [28, 17, 62, 51] , [22, 7, 56, 53] , [10, 9, 34, 39] , [0, 19, 44, 59] ,
                 [20, 3, 60, 47] , [12, 31, 36, 49] , [14, 27, 32, 41] , [24, 5, 42, 55] ,
                 [26, 23, 40, 57] , [2, 1, 46, 45] , [4, 29, 54, 63] , [30, 11, 48, 35] ]


is_box[ 4 ] = [ [26, 19, 60, 53] , [6, 15, 36, 41] , [0, 5, 34, 45] , [20, 25, 58, 63] ,
                 [4, 9, 32, 59] , [18, 17, 54, 61] , [14, 31, 56, 49] , [8, 11, 44, 39] ,
                 [16, 29, 46, 35] , [30, 27, 50, 55] , [10, 23, 40, 57] , [12, 3, 38, 33] ,
                 [2, 7, 52, 37] , [24, 13, 42, 47] , [28, 1, 62, 43] , [22, 21, 48, 51] ]

is_box[ 5 ] = [ [16, 25, 50, 59] , [2, 19, 56, 53] , [10, 7, 40, 37] , [20, 29, 46, 35] ,
                 [22, 5, 52, 33] , [28, 15, 38, 43] , [12, 17, 62, 57] , [26, 9, 48, 55] ,
                 [14, 31, 42, 61] , [8, 13, 32, 41] , [4, 1, 54, 47] , [30, 27, 60, 49] ,
                 [0, 11, 44, 39] , [18, 21, 58, 63] , [24, 23, 34, 51] , [6, 3, 36, 45] ]


is_box[ 6 ] = [ [10, 3, 56, 53] , [30, 13, 32, 41] , [4, 25, 62, 59] , [16, 19, 42, 61] ,
                 [0, 9, 34, 43] , [24, 21, 58, 51] , [28, 31, 52, 33] , [22, 7, 44, 47] ,
                 [12, 29, 54, 39] , [20, 11, 60, 49] , [26, 15, 48, 45] , [2, 5, 36, 35] ,
                 [18, 23, 40, 63] , [14, 1, 38, 37] , [6, 17, 46, 57] , [8, 27, 50, 55] ]


is_box[ 7 ] = [ [26, 25, 48, 55] , [14, 1, 38, 35] , [2, 31, 46, 33] , [20, 11, 58, 57] ,
                 [6, 15, 36, 41] , [24, 19, 60, 59] , [8, 21, 50, 61] , [30, 13, 32, 39] ,
                 [4, 7, 62, 45] , [18, 29, 40, 53] , [16, 9, 52, 43] , [12, 23, 34, 63] ,
                 [28, 17, 42, 51] , [0, 5, 54, 47] , [22, 27, 44, 37] , [10, 3, 56, 49] ]

xormask = []
andmask = []

#generates the 48 bit round keys for each round
def generate_round_keys(encryption_key):

    round_keys = []
    key = encryption_key.deep_copy()
    for round_count in range(2):
        [LKey, RKey] = key.divide_into_two()
        shift = shifts_for_round_key_gen[round_count]
        LKey << shift
        RKey << shift
        key = LKey + RKey
        round_key = key.permute(key_permutation_2)
        round_keys.append(round_key)

    return round_keys


# function that performs s-box substitution
def s_box_sub( expanded_half_block ):

    output = BitVector (size = 32)
    segments = [expanded_half_block[x*6:x*6+6] for x in range(8)]
    for sindex in range(len(segments)):
        row = 2*segments[sindex][0] + segments[sindex][-1]
        column = int(segments[sindex][1:5])
        output[sindex*4:sindex*4+4] = BitVector(intVal = s_boxes[sindex][row][column], size = 4)

    return output

# function for the feistel function for DES
def feistel_DES(RH, round_key):

    expanded_RH = RH.permute(expansion_permutation)
    out_xor = expanded_RH ^ round_key
    out_sboxes = s_box_sub(out_xor)
    output = out_sboxes.permute(p_box_permutation)

    return output

# encryption algorithm for one 64-bit block
def encrypt(round_keys, block):

    for key in round_keys:
        [LH, RH] = block.divide_into_two()
        mod_LH = LH ^ feistel_DES(RH, key)
        block = RH + mod_LH

    # after all the rounds, swap one last time
    [LH, RH] = block.divide_into_two()
    block = RH + LH

    return block

#performs DES encryption or decryption
def DES(keys, cipher_file,output_file,reverse=False):

    round_keys = keys
    if reverse:
        round_keys = round_keys[::-1]

    FILE_OUT = open(output_file, 'ab')

    bv = BitVector(filename = cipher_file)
    while (bv.more_to_read):
        bitvec = bv.read_bits_from_file(64)
        if len(bitvec) > 0:
            if len(bitvec) != 64:
                bitvec.pad_from_right(64-len(bitvec))
            bv_encrypted = encrypt(round_keys, bitvec)
            bv_encrypted.write_to_file(FILE_OUT)
    print("\nDecoded plaintext written to file",output_file)

#function to read file and divide the bitvector into 64 bit blocks
def divide_into_blocks(fname,size):

    veclist=[]
    temp = 0
    bv = BitVector(filename = fname)
    while (bv.more_to_read):
        bitvec = bv.read_bits_from_file(size)
        if len(bitvec) > 0:
            if len(bitvec) != size:
                temp =  temp+len(bitvec)
                bitvec.pad_from_right(size-len(bitvec))
        veclist.append(bitvec)

    return veclist

#function to get the round keys of the known plain and cipher text
def find_round_keys(plaintext, ciphertext):
    """
    Finding the round keys by calculating values in each step within the
    fiestal function using each block of plaintext and ciphertext pair.
    """
    print("\nFINDING ROUND KEYS ...")
    rkey = {i:None for i in range(2)} #keys comman to every block seen so far
    rkey[0] = []
    rkey[1] = []

    plainblocks = divide_into_blocks(plaintext,64)
    cipherblocks = divide_into_blocks(ciphertext,64)

    key_preprocessing()

    for p,c in zip(plainblocks,cipherblocks):

        [pleft,pright] = p.divide_into_two()
        [cleft,cright] = c.divide_into_two()
        f1out  = pleft ^ cright # function output of round 1
        f2out  = pright ^ cleft # function output of round2
        f1in = pright  #input to round 1 fiestal funtion
        f2in = cright #input to round 2 fiestal funtion
        expand_f1in = f1in.permute(expansion_permutation)
        expand_f2in = f2in.permute(expansion_permutation)
        f1out_b4pbox = f1out.unpermute(p_box_permutation)
        f2out_b4pbox = f2out.unpermute(p_box_permutation)
        inverse_sbox_r1 =inverse_sbox(f1out_b4pbox)
        inverse_sbox_r2 =inverse_sbox(f2out_b4pbox)
        possible_keys_r1 = possible_keys(inverse_sbox_r1,expand_f1in,0)
        possible_keys_r2 = possible_keys(inverse_sbox_r2,expand_f2in,1)

        #finding keys common to all blocks seen till now
        if len(rkey[0]) != 0 :
            rkey[0] = list(set(rkey[0]) & set(possible_keys_r1))
        else :
            rkey[0] = list(set(possible_keys_r1) & set(possible_keys_r1))

        if len(rkey[1]) != 0 :
            rkey[1] = list(set(rkey[1]) & set(possible_keys_r2))
        else :
            rkey[1] = list(set(possible_keys_r2) & set(possible_keys_r2))

        #we stop when we narrow down to 1 key per round
        if len(rkey[0]) == 1 and len(rkey[1]) == 1:
            break

    if len(rkey[0]) > 1 and len(rkey[1]) > 1:
        print("More than one possibility for round key found")

    return [BitVector(bitstring = rkey[0][0]),BitVector(bitstring=rkey[1][0])]

#create key mask for testing possible keys
def key_preprocessing():
    # creating a bitmask ,which will be used to test if the
    # corresponding bits have a desired value
    partial_key = "000000a" # we know the last character is "a"
    partial_key_v = BitVector(textstring = partial_key)
    partial_round_keys = generate_round_keys(partial_key_v)
    pos_r1 = [47,48,49,50,51,52,54] # positions of last character in round 1 key
    create_keymask(pos_r1,partial_round_keys[0])
    pos_r2 = [46,47,48,49,50,51,52] # positions of last character in round 2 key
    create_keymask(pos_r2,partial_round_keys[1])

#funtion to enumerate possible inputs to the sboxes for known output
def inverse_sbox(sbox_out):
    """
        Using the 32 bit output of the sbox, we get all possible inputs that
        generated this value. For each 4 bit output value there are 4 possible
        input values that generated it. Therefore for 32 bit output there are
        4^8 = 65536 possible input values.


        The lookup table used in this method for the sboxes have been genrated
        using the following code
        ---------------------------------------------------------------------
            def tobin(row,position):

                middleval = '{0:04b}'.format(position)
                rowval = '{0:02b}'.format(row)
                newval = rowval[0]+middleval+rowval[1]

                return newval

            inverse_box = []
            for i in range(8):
                is_box = []
                for j in range(16):
                    temp = []
                    for k in range(4):
                        temp.append(int(tobin(k,s_boxes[i][k].index(j)),2))
                    is_box.append(temp)
                inverse_box.append(is_box)
        ----------------------------------------------------------------------

    """
    possibility_list_bits = [] # bit vectors of all possible values
    segments = [sbox_out[x*4:x*4+4] for x in range(8)]
    pos = []
    for sindex in range(len(segments)):
        row= int(segments[sindex])
        seg_pos = is_box[sindex][row]
        pos.append(seg_pos)
    cartesian_product = list(itertools.product(pos[0],pos[1],pos[2],pos[3],pos[4],pos[5],pos[6],pos[7]))
    for i in cartesian_product:
        output = BitVector (size=0)
        for j in i:
            output = output+BitVector(intVal = j, size = 6)
        possibility_list_bits.append(output)
    return possibility_list_bits

#funtion to enumerate all possible keys based on known information
def possible_keys(sboxlist,expandedinp,roundnumber):
    """
    Inputs:
        sboxlist(48bit) -> list of all possible sbox input values
        expandedinp(48bit) -> expanded right half

    """
    allkeys = []
    for i in sboxlist:
        key = i ^ expandedinp
        if testkey(key,roundnumber) == 0:
            allkeys.append(str(key))
    return allkeys

#function to test if key will have "a" as the last character in it
def testkey(key,rn):
    """
        Input : key -> possible key under investigation
                rn -> round number when the key was generated

        xor'ing the bitmask with the key will test bit value at
        specific positions;
        and'ing with the xor'ed value will help us conclude that
        and ignore other positions

        return value :  0 -> indicates matches characteristics of desired key
                        1 -> indicates key not what we want
    """
    zerovec = BitVector(intVal=0,size=48)
    val = (key ^ xormask[rn]) & andmask[rn]
    if val == zerovec:
        return 0
    else :
        return 1

#function to create the key mask for known last character
def create_keymask(positions,key):
    """
        creating bitmask from "key",
        based on position values in "positions"
    """
    permuted_pos = {}
    xorm = BitVector(intVal = 0,size = 48)
    andm = BitVector(intVal = 0,size = 48)
    for i in positions:
        pos = key_permutation_2.index(i)
        val = key[pos]
        permuted_pos[pos] = val
    for k in permuted_pos:
        xorm[k] = permuted_pos[k]
        andm[k] = 1
    xormask.append(xorm)
    andmask.append(andm)

if __name__ == "__main__":

    encrypted_file = 'target_ciphertext.txt'
    decrypted_file  = 'target_plaintext.txt'
    decrypt = True

    # delete old versions of encrypted and decrypted file
    if decrypt:
        if os.path.isfile(decrypted_file):
            os.remove(decrypted_file)

    #Getting the 48 bit round keys by known plain text attack
    encryption_round_keys = find_round_keys("sample_plaintext.txt","sample_ciphertext.txt")

    print("\nDECRYPTING TARGET CIPHER TEXT....")
    #decryption
    DES(encryption_round_keys, encrypted_file, decrypted_file, reverse=True)
