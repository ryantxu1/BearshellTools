#!/usr/bin/python

#
# -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
#
#                    [====={ CRYPTO VENOM }=====]
#
#     | ATTENTION!: THIS SOFTWARE IS PART OF THE "CRYPTOVENOM FRAMEWORK" |
#
#              ( https://github.com/lockedbyte/cryptovenom )
#
#           << GNU PUBLIC LICENSE >>
#
#                               / CREATED BY LOCKEDBYTE /
#
#                  [ CONTACT => alejandro.guerrero.rodriguez2@gmail.com ]
#                  [ CONTACT => @LockedByte (Twitter) ]
#
#
# AND NOW...HERE THE CODE
#
# -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
#

from main import *

print('''

-=[OPTIONS]=-

   1) Encrypt
   2) Decrypt
   
''')

opt = input('\033[1;34m[=]\033[0m Option: ')


if opt == '1':


    opt2 = input('\033[1;34m[=]\033[0m [F]ile or [T]ext: ')
    
    if opt2 == 'f' or opt2 == 'F':
    
        importx = 'file'
        exportx = 'file'
        
        text = ''
        
        infile = input('\033[1;34m[=]\033[0m Input file path: ')
        outfile = input('\033[1;34m[=]\033[0m Output file path: ')
    
    
    elif opt2 == 't' or opt2 == 'T':
    
        importx = 'print'
        exportx = 'print'
        infile = ''
        outfile = ''
        
        text = input('\033[1;34m[=]\033[0m Text: ')
    
    
    else:
    
        print('\033[1;31m[-]\033[0m Unknown option')
        exit()
        
    format1 = input('\033[1;34m[=]\033[0m Input format (Eg.: raw or base64): ')
    
    
    out = atbashencode(importx, infile, outfile, format1, exportx, text)
    
    print('\033[1;32m[+]\033[0m Out = ' + str(out))
    print('\033[1;32m[+]\033[0m All done!')


elif opt == '2':


    opt2 = input('\033[1;34m[=]\033[0m [F]ile or [T]ext: ')
    
    if opt2 == 'f' or opt2 == 'F':
    
        importx = 'file'
        exportx = 'file'
        
        text = ''
        
        infile = input('\033[1;34m[=]\033[0m Input file path: ')
        outfile = input('\033[1;34m[=]\033[0m Output file path: ')
    
    
    elif opt2 == 't' or opt2 == 'T':
    
        importx = 'print'
        exportx = 'print'
        infile = ''
        outfile = ''
        
        text = input('\033[1;34m[=]\033[0m Text: ')
    
    
    else:
    
        print('\033[1;31m[-]\033[0m Unknown option')
        exit()
        
    format1 = input('\033[1;34m[=]\033[0m Output format (Eg.: raw or base64): ')
    
    out = atbashdecode(importx, infile, outfile, format1, exportx, text)
    
    print('\033[1;32m[+]\033[0m Out = ' + str(out))
    print('\033[1;32m[+]\033[0m All done!')

else:

    print('\033[1;31m[-]\033[0m Unknown option')
    exit()
