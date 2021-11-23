from typing import List
from functools import reduce
import SHAConstants as sha_const
import hashlib

################################################## UTILITIES ##################################################

def repr(m: List[int]):
  """ Prints an array out as a string of its contents in hexadecimal """
  return ' '.join(list(map(lambda x: hex(x)[2:].zfill(2), m))).upper() # Eg. 12 = '0xc' -> 'c' -> '0c' -> '0C'

def repr2(m: List[List[int]]):
  """ Prints a 2D array out as a string of its contents in hexadecimal, row by row """
  return '\n'.join([' '.join(list(map(lambda x: hex(x)[2:].zfill(2), _m))).upper() for _m in m])

def convert_from_ascii(message: str) -> List[int]:
  """ Converts a string into a list of its characters' ASCII values """
  return list(map(lambda x: ord(x), message))

def convert_to_ascii(block: List[int]) -> str:
  """ Converts a list of ASCII values into the string they represent """
  return ''.join(list(map(lambda x: chr(x), block)))

########################################## TRANSFORMATION OPERATIONS ##########################################

def split_message(message: List[int]) -> List[List[int]]:
  """ Splits a message into a number of blocks of size 64 (-> 512 bits) """
  return [message[i*64:(i+1)*64] for i in range(len(message) // 64 + 1)]

def pad_message(message: List[int]) -> List[int]:
  """ Pads the message to a bit-size divisible by 512. """
  L = len(message)
  # Since we're working with 8-bit character strings, it will always be a block resembling 0b1000_0000.
  pad_start = [1 << 7] 
  length_block = [(L * 8) >> (i * 8) & 0xFF for i in range(7, -1, -1)]

  return message + pad_start + (64 - (L + len(pad_start) + len(length_block)) % 64) * [0] + length_block

def split_to_words(block: List[int]) -> List[List[int]]:
  """ Splits a (n*32) bit-block in n block of 32-bit words."""
  return [block[i*4:(i+1)*4] for i in range(len(block) // 4)]

def w2n(word: List[int]) -> int:
  """ Transforms a 32-bit word into it's numerical representation """
  return word[0] << 24 | word[1] << 16 | word[2] << 8 | word[3]

def n2w(number: int) -> List[int]:
  """ Transforms a number into it's 32-bit word representation """
  return [number >> 24 & 0xFF, number >> 16 & 0xFF, number >> 8 & 0xFF, number & 0xFF]

def rrot(word: List[int], offset: int) -> List[int]:
  """ Performs a cyclic rotation on the word by offset """
  number: int = w2n(word)
  # The right-hand operator here is a way to generate a number which is offset number of 1's in binary.
  left: int = number & sum([1 << i for i in range(offset)])
  right: int = number >> offset
  return n2w(left << (32 - offset) | right)

def rshift(word: List[int], offset: int) -> List[int]:
  """ Performs a right shift on word by offset """
  return n2w(w2n(word) >> offset)

############################################## BITWISE OPERATIONS #############################################

def op_xor(*values: List[List[int]]) -> List[int]:
  """ Performs a linear XOR among a number of lists of same size. """
  assert min(list(map(len, values))) == max(list(map(len, values))), 'Cannot op_xor Lists, different list sizes.'
  return [reduce(lambda x, y: x ^ y, map(lambda z: z[i], values)) for i in range(min(list(map(len, values))))]

def op_and(*values: List[List[int]]) -> List[int]:
  """ Performs a linear AND among a number of lists of same size. """
  assert min(list(map(len, values))) == max(list(map(len, values))), 'Cannot AND Lists, different list sizes.'
  return [reduce(lambda x, y: x & y, map(lambda z: z[i], values)) for i in range(min(list(map(len, values))))]

def op_not(value: List[int]) -> List[int]:
  """ Performs a NOT on a number. """
  return list(map(lambda x: ~x & 0xFF, value))

############################################## MAIN PROGRAM ELEMENTS ##############################################

def owf_compression(block: List[int], vector: List[int]) -> List[int]:
  """ One-way-function for compression that takes a 512-bit block from the message and a 256-bit cipher vector """
  words: List[List[int]] = split_to_words(block)
  vector_words: List[List[int]] = split_to_words(vector)
  
  for i in range(16, 64):
    s0: List[int] = op_xor(rrot(words[i-15], 7), rrot(words[i-15], 18), rshift(words[i-15], 3))
    s1: List[int] = op_xor(rrot(words[i-2], 17), rrot(words[i-2], 19), rshift(words[i-2], 10))

    words += [n2w((w2n(words[i-16]) + w2n(s0) + w2n(words[i-7]) + w2n(s1)) % 2**32)]

  a, b, c, d, e, f, g, h = vector_words

  # Compression part
  for i in range(64):
    X1: List[int] = op_xor(rrot(e, 6), rrot(e, 11), rrot(e, 25))
    CH: List[int] = op_xor(op_and(e, f), op_and(op_not(e), g))
    X2: List[int] = op_xor(rrot(a, 2), rrot(a, 13), rrot(a, 22))
    MAJ: List[int] = op_xor(op_and(a, b), op_and(a, c), op_and(b, c))
    temp1: List[int] = n2w(sum(list(map(lambda x: w2n(x), [h, X1, CH, n2w(sha_const.K[i]), words[i]]))) % 2**32)
    temp2: List[int] = n2w(sum(list(map(lambda x: w2n(x), [X2, MAJ]))) % 2**32)
    h, g, f = g, f, e
    e = n2w((w2n(d) + w2n(temp1)) % 2**32)
    d, c, b = c, b, a
    a = n2w((w2n(temp1) + w2n(temp2)) % 2**32)
  
  elements = [a, b, c, d, e, f, g, h]
  output = [n2w((w2n(vector_words[i]) + w2n(elements[i])) % 2**32) for i in range(8)]
  
  return [el for arr in output for el in arr]

def _sha_256_hash(message: List[int]) -> List[int]:
  """ Pads, splits into blocks and performs the one-way hashing function on all of the blocks. """
  padded: List[int] = pad_message(message)
  blocks: List[List[int]] = split_message(padded)
  hash_value: List[int] = 32 * [0]

  for i in range(len(blocks) - 1):
    hash_value = owf_compression(blocks[i], [el for arr in list(map(lambda x: n2w(x), sha_const.IV)) for el in arr] if i == 0 else hash_value)

  return hash_value

def sha_256_hash(message: str) -> List[int]:
  return _sha_256_hash(convert_from_ascii(message))

def test(message: str):
  print(f'IN: "{message}"')
  sha_value = sha_256_hash(message)
  print(f'OUT: ({repr(sha_value)})_16')
  assert ''.join(list(map(lambda x: hex(x)[2:].zfill(2), sha_value))).lower() == hashlib.sha256(message.encode("ascii")).hexdigest(), 'SHA-256 does not correspond with values computed using the real algorithm.'
  print()

if __name__ == '__main__':
  test('')
  test('Welcome to Wrestlemania!')
  test('Fight for your dreams, and your dreams will fight for you!')
