from main import *
from bruteforce import *

print('''

-=[OPTIONS]=-

   1) Hash Encrypt
   
   2) Hash Brute Force
   
   ''')
   
opt = input('\033[1;34m[=]\033[0m Option: ')


hash1 = input('\033[1;34m[=]\033[0m Hash/Text: ')



if opt == '1':
    f0rmat = input('\033[1;34m[=]\033[0m Output format (Eg.: hex): ')
    h = md4(f0rmat, 'print', 'raw', hash1, '', '')
    print('\033[1;32m[+]\033[0m h(x) = ' + h)

elif opt == '2':

    dic = input('\033[1;34m[=]\033[0m Dictionary path: ')

    bf(hash1, dic)

else:

    print('\033[1;31m[-]\033[0m Unknown option')
