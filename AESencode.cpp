/* AES Encryption Implementation (with 128-bit keys).
Specification source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf

Todo:
-Implement cipher block chaining, which means identical 16-byte blocks in the same file don't translate
    the same - avoiding patterns

-Encrypt to base 64, instead of hex

-Decrypt as well as encrypt

-Add 192-bit and 256-bit keys
*/

#include <iostream> //user dialog
#include <fstream> //input + output data
#include <string> //convert input to hex
#include <array> //allows functions to return arrays 

using namespace std;

typedef unsigned char u8;
typedef unsigned int u32;

//In AES, bytes are not treated as integers but part of a 
//"Galois field", a finite set of numbers with substitutes for addition
//and multiplication such that the results remain within the set.
//Specifically we use Rijndael's field, which contains 0-255 (2**8 - 1),
//and where addition is replaced by xor. Multiplication uses the standard binary
//multiplication method, but with xor instead of + and modulo 0x11b.
u8 rijndael_multiply(u8 a, u8 b)
{
    const int reducing_num = 0x11b;
    short int result = 0;
    for (int i = 0; i <= 7; i++) //binary multiply
    {
        if ((b & (1 << i)) == (1 << i))
        {
            result ^= (a << i);
        }
    }

    for (int i = 15; i >= 8; i--) //modulus equivalent
    {
        if ((result & (1 << i)) == (1 << i))
        {
            result ^= (reducing_num << (i - 8));
        }
    }
    return result;
}

//In a Galois field with 256 elements a**255 = 1 for a =/= 0,
// so a**254 = a**-1.
u8 rijndael_inverse(u8 x)
{
    u8 result = 1;
    for (int i = 1; i <= 254; i++)
    {
        result = rijndael_multiply(result, x);
    }
    return result;
}

//Shifts each bit of x to the left y times (and sends the front to the back)
u8 lcs_8bit(u8 x, u8 y) //Used to calculate the S-box
{
    return ((x << y) % 0x100) + (x >> (8 - y));
}

//Same but with 4 bytes instead of 8 bits
array<u8, 4> lcs_4byte(array<u8, 4> x, u8 y)
{ //Used to generate the key schedule
    for (int i = 1; i <= y; i++)
    {
        x = { x[1], x[2], x[3], x[0] };
    }
    return x;
}

//The S-box is a nonlinear transformation used in all 10 rounds of the encryption,
//and in generating the keys for each round.
u8 sbox_value(u8 input)
{
    u8 inv = rijndael_inverse(input);
    u8 result = inv ^ lcs_8bit(inv, 1) ^ lcs_8bit(inv, 2) ^ lcs_8bit(inv, 3) ^ lcs_8bit(inv, 4) ^ 0x63;
    return result;
}

//store the s-box as an array rather than a function
u8 sbox[256];
void make_sbox_array()
{
    for (int i = 0; i <= 0xff; i++)
    {
        sbox[i] = sbox_value(i);
    }
}

//The round constants are a series of bytes used in computing the keys
//for each round.
u8 round_constant(char i)
{
    if (i == 1)
    {
        return 1;
    }
    else
    {
        u8 previous_rc = round_constant(i - 1);
        if (previous_rc < 128)
        {
            return (2 * previous_rc);
        }
        else
        {
            return (((2 * previous_rc) - 256) ^ 0x1b);
        }
    }
}

//This AES uses 10 rounds - each round uses a different 16-byte key which
//is an evolution of the last's key. This function takes the original
//key and returns it plus the 10 other keys.
array<u8, 176> key_schedule;
void make_key_schedule(array<u8, 16> key)
{
    array<u8, 4> o1; //1 byte ago
    array<u8, 4> o4; //4 bytes ago

    for (char i = 0; i < 44; i++)
    {
        if (i < 4)
        {
            memcpy(&key_schedule[i * 4], &key[i * 4], 4);
        }
        else
        {
            memcpy(&o1, &key_schedule[(i - 1) * 4], 4);
            memcpy(&o4, &key_schedule[(i - 4) * 4], 4);
            if ((i % 4) == 0)
            {
                array<u8, 4> rot = lcs_4byte(o1, 1);
                array<u8, 4> s = { sbox[rot[0]], sbox[rot[1]], sbox[rot[2]], sbox[rot[3]] };
                array<u8, 4> rc_array = { round_constant(i / 4), 0x00, 0x00, 0x00 };
                for (int j = 0; j < 4; j++)
                {
                    key_schedule[4 * i + j] = o4[j] ^ s[j] ^ (rc_array[j]);
                }
            }
            else
            {
                for (int j = 0; j < 4; j++)
                {
                    key_schedule[4 * i + j] = o1[j] ^ o4[j];
                }
            }
        }

    }
}

array<u8, 16> encrypt_message(array<u8, 16> input)
{
    array<u8, 16>round_key;

    //Step 0
    memcpy(&round_key, &key_schedule, 16);
    for (int i = 0; i < 16; i++)
    {
        input[i] ^= round_key[i];
    }
    //Step 1..10
    for (int round = 1; round <= 10; round++)
    {
        //"SubBytes" - perform the S-box transformation
        for (int i = 0; i < 16; i++)
        {
            input[i] = sbox[input[i]];
        }

        //The next two steps are done treating the block as a 4x4 matrix, filling columns first, then rows
        //"ShiftRows" - does a left shift on row x (where x goes from 0 to 3) by x bytes.
        for (int i = 0; i < 4; i++)
        {
            array<u8, 4> newrow = lcs_4byte({ input[i], input[i + 4], input[i + 8], input[i + 12] }, i);
            input[i] = newrow[0];
            input[i + 4] = newrow[1];
            input[i + 8] = newrow[2];
            input[i + 12] = newrow[3];
        }
        //"MixColumns" - a linear transformation on each column
        if (round != 10)
        {
            for (int i = 0; i < 4; i++)
            {
                array <u8, 4> mix;
                mix[0] = rijndael_multiply(2, input[4 * i]) ^ rijndael_multiply(3, input[4 * i + 1]) ^ input[4 * i + 2] ^ input[4 * i + 3];
                mix[1] = input[4 * i] ^ rijndael_multiply(2, input[4 * i + 1]) ^ rijndael_multiply(3, input[4 * i + 2]) ^ input[4 * i + 3];
                mix[2] = input[4 * i] ^ input[4 * i + 1] ^ rijndael_multiply(2, input[4 * i + 2]) ^ rijndael_multiply(3, input[4 * i + 3]);
                mix[3] = rijndael_multiply(3, input[4 * i]) ^ input[4 * i + 1] ^ input[4 * i + 2] ^ rijndael_multiply(2, input[4 * i + 3]);
                memcpy(&input[4 * i], &mix, 4);
            }
        }

        //"AddRoundKey" - xor each byte with its corresponding round key byte
        memcpy(&round_key, &key_schedule[round * 16], 16);
        for (int i = 0; i < 16; i++)
        {
            input[i] ^= round_key[i];
        }
    }
    return input;
}

array<u8, 16> user_key;
int main(int argc, char **argv)
{
    make_sbox_array();

    ifstream input_file;
    ofstream output_file;
    string input_filename, output_filename;
    do
    { //File input loop
        cout << endl << "Enter a file name: ";
        cin >> input_filename;
        input_file.open(input_filename);
    } while (input_file.fail());

    int dot_pos = input_filename.find('.'); //append _aes to the name, for the encrypted output file
    output_filename = input_filename.substr(0, dot_pos) + "_aes" + input_filename.substr(dot_pos);

    string key_input;
    do //Key input loop
    {
        key_input = "";
        cout << endl <<  "Enter a key - 32 hex characters: ";
        cin >> key_input;
    } while ((key_input.length() != 32) || (strspn(key_input.c_str(), "1234567890abcdefABCDEF") != 32));
    //Prompt user until the input string has 32 characters, all of which are valid hex digits

    for (int i = 0; i < 16; i++)
    { // Convert input to key, from two characters at a time to one byte at a time
        user_key[i] = stoi(key_input.substr(2 * i, 2), nullptr, 16);
    }

    cout << endl << "Encrypting..." << endl;

    make_key_schedule(user_key); //Generate the round keys

    char buffer[16];
    array<u8, 16> block;
    output_file.open(output_filename);
    while (input_file)
    {
        //Read the input file, in blocks 16 characters at a time
        input_file.read(buffer, 16);
        if (!input_file)
        {   //If the file ends before 16 characters, fill the rest of the block with zeros
            int chars_left = input_file.gcount();
            if (chars_left == 0)
            {
                break;
            }
            else
            {
                for (int i = input_file.gcount(); i < 16; i++)
                {
                    buffer[i] = 0x00;
                }
            }
        }
        for (int i = 0; i < 16; i++)
        {   //convert from signed to unsigned char
            block[i] = (u8)buffer[i];
        }
        
        array<u8, 16> encrypt = encrypt_message(block);
        for (int i = 0; i < 16; i++)
        {   //write encrypted block to the output file as hex characters
            output_file << hex << int(encrypt[i]);
        }
    }
    input_file.close();
    output_file.close();

    cout << "Completed!" << endl;
}
