# ChosenPlaintextAttack-DES2rounds

The goal here was to understand the importance of performing multiple Fiestal rounds in DES.

The DES performs 16 rounds. . This implementation uses only 2 rounds instead of 16 rounds.

we already have a pair of plaintext and a corresponding cipheterext pair in the files sample_plaintext.txt and sample_ciphertext.txt respectively. The ciphertext has been generated using the DES algorithm with 2 rounds only. The 56-bit key used for encryption is derived for a password containing exactly 7 ascii characters (8 bit character), where the last character of the password is the character 'a'. Please note that the password contains ascii characters not the alphabets. The task here is to find
the plaintext of the ciphertext given in the file named target_ciphertext.txt . The last character of the password is reveled to reduce your effort of performing bruteforce attack and make the attack feasible.
