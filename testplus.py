# p1 test cases; test case number is the suffix on the variable
# test with your streetCSP's isValid method
# each test case is a tuple containing:
# (assignment, reference_solution)
p1_00 = ({'A1': 'F', 'A3': 'S', 'A2': 'H', 'A5': 'Z', 'A4': 'D', 'C3': 'R', 'C2': 'B', 'C1': 'Y', 'C5': 'G', 'C4': 'W', 'N1': 'N', 'N2': 'I', 'N3': 'E', 'N4': 'S', 'N5': 'J', 'J4': 'V', 'J5': 'P', 'J1': 'Di', 'J2': 'Do', 'J3': 'S', 'D4': 'F', 'D5': 'C', 'D2': 'T', 'D3': 'M', 'D1': 'W'}, True)
p1_01 = ({'A1': 'D', 'A3': 'H', 'A2': 'F', 'A5': 'S', 'A4': 'Z', 'C3': 'G', 'C2': 'B', 'C1': 'Y', 'C5': 'R', 'C4': 'W', 'N1': 'N', 'N2': 'I', 'N3': 'S', 'N4': 'E', 'N5': 'J', 'J4': 'V', 'J5': 'Di', 'J1': 'P', 'J2': 'S', 'J3': 'Do', 'D4': 'C', 'D5': 'F', 'D2': 'T', 'D3': 'W', 'D1': 'M'}, False)
p1_02 = ({'A1': 'D', 'A3': 'H', 'A2': 'F', 'A5': 'S', 'A4': 'Z', 'C3': 'W', 'C2': 'B', 'C1': 'R', 'C5': 'Y', 'C4': 'G', 'N1': 'E', 'N2': 'J', 'N3': 'S', 'N4': 'N', 'N5': 'I', 'J4': 'Di', 'J5': 'P', 'J1': 'V', 'J2': 'S', 'J3': 'Do', 'D4': 'W', 'D5': 'M', 'D2': 'F', 'D3': 'C', 'D1': 'T'}, False)
p1_03 = ({'A1': 'D', 'A3': 'H', 'A2': 'S', 'A5': 'F', 'A4': 'Z', 'C3': 'B', 'C2': 'W', 'C1': 'Y', 'C5': 'R', 'C4': 'G', 'N1': 'E', 'N2': 'N', 'N3': 'I', 'N4': 'S', 'N5': 'J', 'J4': 'P', 'J5': 'V', 'J1': 'Do', 'J2': 'S', 'J3': 'Di', 'D4': 'C', 'D5': 'F', 'D2': 'M', 'D3': 'T', 'D1': 'W'}, False)
p1_04 = ({'A1': 'D', 'A3': 'F', 'A2': 'H', 'A5': 'Z', 'A4': 'S', 'C3': 'Y', 'C2': 'W', 'C1': 'R', 'C5': 'G', 'C4': 'B', 'N1': 'N', 'N2': 'S', 'N3': 'I', 'N4': 'E', 'N5': 'J', 'J4': 'S', 'J5': 'P', 'J1': 'V', 'J2': 'Di', 'J3': 'Do', 'D4': 'F', 'D5': 'T', 'D2': 'M', 'D3': 'W', 'D1': 'C'}, False)
p1_05 = ({'A1': 'Z', 'A3': 'F', 'A2': 'H', 'A5': 'D', 'A4': 'S', 'C3': 'R', 'C2': 'W', 'C1': 'B', 'C5': 'G', 'C4': 'Y', 'N1': 'S', 'N2': 'I', 'N3': 'E', 'N4': 'N', 'N5': 'J', 'J4': 'Di', 'J5': 'S', 'J1': 'Do', 'J2': 'P', 'J3': 'V', 'D4': 'C', 'D5': 'M', 'D2': 'F', 'D3': 'T', 'D1': 'W'}, False)
p1_06 = ({'A1': 'F', 'A3': 'S', 'A2': 'H', 'A5': 'Z', 'A4': 'D', 'C3': 'W', 'C2': 'R', 'C1': 'Y', 'C5': 'B', 'C4': 'G', 'N1': 'E', 'N2': 'J', 'N3': 'I', 'N4': 'N', 'N5': 'S', 'J4': 'Do', 'J5': 'S', 'J1': 'Di', 'J2': 'P', 'J3': 'V', 'D4': 'C', 'D5': 'F', 'D2': 'M', 'D3': 'W', 'D1': 'T'}, False)
p1_07 = ({'A1': 'H', 'A3': 'F', 'A2': 'D', 'A5': 'Z', 'A4': 'S', 'C3': 'Y', 'C2': 'B', 'C1': 'W', 'C5': 'R', 'C4': 'G', 'N1': 'S', 'N2': 'N', 'N3': 'E', 'N4': 'J', 'N5': 'I', 'J4': 'P', 'J5': 'S', 'J1': 'V', 'J2': 'Di', 'J3': 'Do', 'D4': 'T', 'D5': 'W', 'D2': 'M', 'D3': 'C', 'D1': 'F'}, False)
p1_08 = ({'A1': 'H', 'A3': 'Z', 'A2': 'F', 'A5': 'D', 'A4': 'S', 'C3': 'B', 'C2': 'R', 'C1': 'G', 'C5': 'Y', 'C4': 'W', 'N1': 'I', 'N2': 'J', 'N3': 'S', 'N4': 'E', 'N5': 'N', 'J4': 'Di', 'J5': 'V', 'J1': 'P', 'J2': 'S', 'J3': 'Do', 'D4': 'M', 'D5': 'C', 'D2': 'T', 'D3': 'W', 'D1': 'F'}, False)
p1_09 = ({'A1': 'F', 'A3': 'S', 'A2': 'D', 'A5': 'H', 'A4': 'Z', 'C3': 'B', 'C2': 'W', 'C1': 'R', 'C5': 'G', 'C4': 'Y', 'N1': 'E', 'N2': 'S', 'N3': 'J', 'N4': 'N', 'N5': 'I', 'J4': 'V', 'J5': 'Do', 'J1': 'P', 'J2': 'S', 'J3': 'Di', 'D4': 'T', 'D5': 'F', 'D2': 'W', 'D3': 'C', 'D1': 'M'}, False)
p1_10 = ({'A1': 'S', 'A3': 'F', 'A2': 'D', 'A5': 'H', 'A4': 'Z', 'C3': 'G', 'C2': 'Y', 'C1': 'B', 'C5': 'R', 'C4': 'W', 'N1': 'N', 'N2': 'S', 'N3': 'I', 'N4': 'E', 'N5': 'J', 'J4': 'Di', 'J5': 'Do', 'J1': 'V', 'J2': 'P', 'J3': 'S', 'D4': 'F', 'D5': 'T', 'D2': 'M', 'D3': 'C', 'D1': 'W'}, False)
p1_11 = ({'A1': 'S', 'A3': 'Z', 'A2': 'F', 'A5': 'H', 'A4': 'D', 'C3': 'G', 'C2': 'Y', 'C1': 'B', 'C5': 'W', 'C4': 'R', 'N1': 'I', 'N2': 'S', 'N3': 'E', 'N4': 'J', 'N5': 'N', 'J4': 'Di', 'J5': 'S', 'J1': 'P', 'J2': 'V', 'J3': 'Do', 'D4': 'M', 'D5': 'W', 'D2': 'C', 'D3': 'F', 'D1': 'T'}, False)
p1_12 = ({'A1': 'F', 'A3': 'S', 'A2': 'H', 'A5': 'D', 'A4': 'Z', 'C3': 'Y', 'C2': 'B', 'C1': 'W', 'C5': 'G', 'C4': 'R', 'N1': 'E', 'N2': 'J', 'N3': 'S', 'N4': 'N', 'N5': 'I', 'J4': 'Di', 'J5': 'Do', 'J1': 'V', 'J2': 'P', 'J3': 'S', 'D4': 'C', 'D5': 'T', 'D2': 'M', 'D3': 'W', 'D1': 'F'}, False)
p1_13 = ({'A1': 'S', 'A3': 'H', 'A2': 'Z', 'A5': 'F', 'A4': 'D', 'C3': 'G', 'C2': 'B', 'C1': 'Y', 'C5': 'R', 'C4': 'W', 'N1': 'N', 'N2': 'I', 'N3': 'E', 'N4': 'S', 'N5': 'J', 'J4': 'Di', 'J5': 'P', 'J1': 'V', 'J2': 'Do', 'J3': 'S', 'D4': 'W', 'D5': 'C', 'D2': 'M', 'D3': 'T', 'D1': 'F'}, False)
p1_14 = ({'A1': 'Z', 'A3': 'H', 'A2': 'D', 'A5': 'S', 'A4': 'F', 'C3': 'W', 'C2': 'G', 'C1': 'Y', 'C5': 'R', 'C4': 'B', 'N1': 'J', 'N2': 'E', 'N3': 'I', 'N4': 'S', 'N5': 'N', 'J4': 'S', 'J5': 'Do', 'J1': 'P', 'J2': 'Di', 'J3': 'V', 'D4': 'M', 'D5': 'F', 'D2': 'T', 'D3': 'W', 'D1': 'C'}, False)
p1_15 = ({'A1': 'Z', 'A3': 'F', 'A2': 'H', 'A5': 'S', 'A4': 'D', 'C3': 'R', 'C2': 'W', 'C1': 'G', 'C5': 'Y', 'C4': 'B', 'N1': 'E', 'N2': 'I', 'N3': 'S', 'N4': 'N', 'N5': 'J', 'J4': 'V', 'J5': 'S', 'J1': 'Do', 'J2': 'P', 'J3': 'Di', 'D4': 'M', 'D5': 'F', 'D2': 'W', 'D3': 'C', 'D1': 'T'}, False)
p1_16 = ({'A1': 'H', 'A3': 'Z', 'A2': 'F', 'A5': 'D', 'A4': 'S', 'C3': 'Y', 'C2': 'G', 'C1': 'B', 'C5': 'R', 'C4': 'W', 'N1': 'S', 'N2': 'J', 'N3': 'N', 'N4': 'I', 'N5': 'E', 'J4': 'V', 'J5': 'P', 'J1': 'Di', 'J2': 'Do', 'J3': 'S', 'D4': 'F', 'D5': 'C', 'D2': 'T', 'D3': 'M', 'D1': 'W'}, False)
p1_17 = ({'A1': 'D', 'A3': 'S', 'A2': 'H', 'A5': 'Z', 'A4': 'F', 'C3': 'B', 'C2': 'W', 'C1': 'G', 'C5': 'Y', 'C4': 'R', 'N1': 'J', 'N2': 'E', 'N3': 'I', 'N4': 'N', 'N5': 'S', 'J4': 'P', 'J5': 'V', 'J1': 'S', 'J2': 'Di', 'J3': 'Do', 'D4': 'W', 'D5': 'M', 'D2': 'C', 'D3': 'T', 'D1': 'F'}, False)
p1_18 = ({'A1': 'D', 'A3': 'S', 'A2': 'Z', 'A5': 'H', 'A4': 'F', 'C3': 'B', 'C2': 'G', 'C1': 'Y', 'C5': 'R', 'C4': 'W', 'N1': 'E', 'N2': 'S', 'N3': 'J', 'N4': 'I', 'N5': 'N', 'J4': 'V', 'J5': 'Do', 'J1': 'Di', 'J2': 'S', 'J3': 'P', 'D4': 'F', 'D5': 'M', 'D2': 'W', 'D3': 'C', 'D1': 'T'}, False)
p1_19 = ({'A1': 'Z', 'A3': 'D', 'A2': 'H', 'A5': 'S', 'A4': 'F', 'C3': 'Y', 'C2': 'R', 'C1': 'B', 'C5': 'W', 'C4': 'G', 'N1': 'S', 'N2': 'E', 'N3': 'N', 'N4': 'J', 'N5': 'I', 'J4': 'Do', 'J5': 'Di', 'J1': 'P', 'J2': 'S', 'J3': 'V', 'D4': 'W', 'D5': 'C', 'D2': 'M', 'D3': 'T', 'D1': 'F'}, False)
p1_20 = ({'A1': 'F', 'A3': 'H', 'A2': 'S', 'A5': 'Z', 'A4': 'D', 'C3': 'W', 'C2': 'B', 'C1': 'G', 'C5': 'Y', 'C4': 'R', 'N1': 'J', 'N2': 'I', 'N3': 'E', 'N4': 'S', 'N5': 'N', 'J4': 'S', 'J5': 'V', 'J1': 'Di', 'J2': 'Do', 'J3': 'P', 'D4': 'C', 'D5': 'T', 'D2': 'W', 'D3': 'F', 'D1': 'M'}, False)
p1_21 = ({'A1': 'D', 'A3': 'S', 'A2': 'F', 'A5': 'H', 'A4': 'Z', 'C3': 'B', 'C2': 'R', 'C1': 'Y', 'C5': 'W', 'C4': 'G', 'N1': 'J', 'N2': 'S', 'N3': 'E', 'N4': 'I', 'N5': 'N', 'J4': 'Do', 'J5': 'Di', 'J1': 'S', 'J2': 'P', 'J3': 'V', 'D4': 'T', 'D5': 'W', 'D2': 'M', 'D3': 'C', 'D1': 'F'}, False)
p1_22 = ({'A1': 'D', 'A3': 'F', 'A2': 'S', 'A5': 'Z', 'A4': 'H', 'C3': 'B', 'C2': 'R', 'C1': 'G', 'C5': 'W', 'C4': 'Y', 'N1': 'E', 'N2': 'S', 'N3': 'N', 'N4': 'J', 'N5': 'I', 'J4': 'V', 'J5': 'Di', 'J1': 'P', 'J2': 'S', 'J3': 'Do', 'D4': 'T', 'D5': 'M', 'D2': 'C', 'D3': 'F', 'D1': 'W'}, False)
p1_23 = ({'A1': 'S', 'A3': 'H', 'A2': 'F', 'A5': 'Z', 'A4': 'D', 'C3': 'Y', 'C2': 'R', 'C1': 'G', 'C5': 'W', 'C4': 'B', 'N1': 'S', 'N2': 'N', 'N3': 'I', 'N4': 'E', 'N5': 'J', 'J4': 'P', 'J5': 'Di', 'J1': 'V', 'J2': 'S', 'J3': 'Do', 'D4': 'F', 'D5': 'T', 'D2': 'W', 'D3': 'M', 'D1': 'C'}, False)
p1_24 = ({'A1': 'D', 'A3': 'H', 'A2': 'Z', 'A5': 'S', 'A4': 'F', 'C3': 'Y', 'C2': 'R', 'C1': 'G', 'C5': 'B', 'C4': 'W', 'N1': 'E', 'N2': 'N', 'N3': 'S', 'N4': 'J', 'N5': 'I', 'J4': 'Di', 'J5': 'V', 'J1': 'Do', 'J2': 'P', 'J3': 'S', 'D4': 'C', 'D5': 'T', 'D2': 'M', 'D3': 'W', 'D1': 'F'}, False)
p1_25 = ({'A1': 'F', 'A3': 'H', 'A2': 'S', 'A5': 'Z', 'A4': 'D', 'C3': 'W', 'C2': 'R', 'C1': 'G', 'C5': 'B', 'C4': 'Y', 'N1': 'E', 'N2': 'I', 'N3': 'S', 'N4': 'J', 'N5': 'N', 'J4': 'S', 'J5': 'Di', 'J1': 'V', 'J2': 'Do', 'J3': 'P', 'D4': 'M', 'D5': 'T', 'D2': 'F', 'D3': 'W', 'D1': 'C'}, False)
p1_26 = ({'A1': 'H', 'A3': 'F', 'A2': 'S', 'A5': 'D', 'A4': 'Z', 'C3': 'G', 'C2': 'W', 'C1': 'Y', 'C5': 'B', 'C4': 'R', 'N1': 'E', 'N2': 'I', 'N3': 'S', 'N4': 'N', 'N5': 'J', 'J4': 'Do', 'J5': 'V', 'J1': 'Di', 'J2': 'P', 'J3': 'S', 'D4': 'M', 'D5': 'F', 'D2': 'C', 'D3': 'T', 'D1': 'W'}, False)
p1_27 = ({'A1': 'H', 'A3': 'F', 'A2': 'Z', 'A5': 'D', 'A4': 'S', 'C3': 'G', 'C2': 'Y', 'C1': 'R', 'C5': 'W', 'C4': 'B', 'N1': 'S', 'N2': 'N', 'N3': 'J', 'N4': 'E', 'N5': 'I', 'J4': 'Di', 'J5': 'S', 'J1': 'Do', 'J2': 'V', 'J3': 'P', 'D4': 'W', 'D5': 'M', 'D2': 'C', 'D3': 'T', 'D1': 'F'}, False)
p1_28 = ({'A1': 'D', 'A3': 'H', 'A2': 'Z', 'A5': 'F', 'A4': 'S', 'C3': 'Y', 'C2': 'R', 'C1': 'B', 'C5': 'W', 'C4': 'G', 'N1': 'I', 'N2': 'N', 'N3': 'S', 'N4': 'J', 'N5': 'E', 'J4': 'S', 'J5': 'P', 'J1': 'Di', 'J2': 'Do', 'J3': 'V', 'D4': 'M', 'D5': 'C', 'D2': 'W', 'D3': 'F', 'D1': 'T'}, False)
p1_29 = ({'A1': 'S', 'A3': 'D', 'A2': 'Z', 'A5': 'F', 'A4': 'H', 'C3': 'G', 'C2': 'Y', 'C1': 'B', 'C5': 'W', 'C4': 'R', 'N1': 'E', 'N2': 'N', 'N3': 'I', 'N4': 'J', 'N5': 'S', 'J4': 'P', 'J5': 'Di', 'J1': 'V', 'J2': 'S', 'J3': 'Do', 'D4': 'W', 'D5': 'M', 'D2': 'T', 'D3': 'F', 'D1': 'C'}, False)
p1_30 = ({'A1': 'D', 'A3': 'S', 'A2': 'F', 'A5': 'H', 'A4': 'Z', 'C3': 'G', 'C2': 'B', 'C1': 'W', 'C5': 'Y', 'C4': 'R', 'N1': 'N', 'N2': 'S', 'N3': 'I', 'N4': 'J', 'N5': 'E', 'J4': 'P', 'J5': 'S', 'J1': 'Di', 'J2': 'V', 'J3': 'Do', 'D4': 'T', 'D5': 'C', 'D2': 'F', 'D3': 'W', 'D1': 'M'}, False)
p1_31 = ({'A1': 'S', 'A3': 'Z', 'A2': 'H', 'A5': 'F', 'A4': 'D', 'C3': 'B', 'C2': 'G', 'C1': 'Y', 'C5': 'W', 'C4': 'R', 'N1': 'J', 'N2': 'E', 'N3': 'S', 'N4': 'I', 'N5': 'N', 'J4': 'V', 'J5': 'S', 'J1': 'Di', 'J2': 'Do', 'J3': 'P', 'D4': 'W', 'D5': 'T', 'D2': 'F', 'D3': 'M', 'D1': 'C'}, False)
p1_32 = ({'A1': 'H', 'A3': 'Z', 'A2': 'S', 'A5': 'F', 'A4': 'D', 'C3': 'B', 'C2': 'R', 'C1': 'W', 'C5': 'G', 'C4': 'Y', 'N1': 'I', 'N2': 'J', 'N3': 'E', 'N4': 'N', 'N5': 'S', 'J4': 'Di', 'J5': 'V', 'J1': 'S', 'J2': 'P', 'J3': 'Do', 'D4': 'F', 'D5': 'W', 'D2': 'C', 'D3': 'T', 'D1': 'M'}, False)
p1_33 = ({'A1': 'Z', 'A3': 'D', 'A2': 'F', 'A5': 'S', 'A4': 'H', 'C3': 'Y', 'C2': 'R', 'C1': 'G', 'C5': 'B', 'C4': 'W', 'N1': 'J', 'N2': 'N', 'N3': 'E', 'N4': 'S', 'N5': 'I', 'J4': 'S', 'J5': 'Di', 'J1': 'V', 'J2': 'Do', 'J3': 'P', 'D4': 'C', 'D5': 'F', 'D2': 'W', 'D3': 'T', 'D1': 'M'}, False)
p1_34 = ({'A1': 'H', 'A3': 'D', 'A2': 'F', 'A5': 'Z', 'A4': 'S', 'C3': 'W', 'C2': 'G', 'C1': 'Y', 'C5': 'R', 'C4': 'B', 'N1': 'J', 'N2': 'E', 'N3': 'S', 'N4': 'I', 'N5': 'N', 'J4': 'Di', 'J5': 'P', 'J1': 'V', 'J2': 'Do', 'J3': 'S', 'D4': 'F', 'D5': 'T', 'D2': 'M', 'D3': 'C', 'D1': 'W'}, False)
p1_35 = ({'A1': 'D', 'A3': 'F', 'A2': 'Z', 'A5': 'S', 'A4': 'H', 'C3': 'B', 'C2': 'W', 'C1': 'R', 'C5': 'G', 'C4': 'Y', 'N1': 'S', 'N2': 'J', 'N3': 'I', 'N4': 'N', 'N5': 'E', 'J4': 'P', 'J5': 'S', 'J1': 'Di', 'J2': 'V', 'J3': 'Do', 'D4': 'T', 'D5': 'F', 'D2': 'M', 'D3': 'W', 'D1': 'C'}, False)
p1_36 = ({'A1': 'H', 'A3': 'D', 'A2': 'S', 'A5': 'Z', 'A4': 'F', 'C3': 'W', 'C2': 'B', 'C1': 'G', 'C5': 'R', 'C4': 'Y', 'N1': 'I', 'N2': 'J', 'N3': 'N', 'N4': 'E', 'N5': 'S', 'J4': 'P', 'J5': 'V', 'J1': 'S', 'J2': 'Di', 'J3': 'Do', 'D4': 'T', 'D5': 'F', 'D2': 'C', 'D3': 'W', 'D1': 'M'}, False)
p1_37 = ({'A1': 'D', 'A3': 'S', 'A2': 'H', 'A5': 'F', 'A4': 'Z', 'C3': 'B', 'C2': 'G', 'C1': 'W', 'C5': 'R', 'C4': 'Y', 'N1': 'J', 'N2': 'S', 'N3': 'E', 'N4': 'N', 'N5': 'I', 'J4': 'P', 'J5': 'Do', 'J1': 'S', 'J2': 'Di', 'J3': 'V', 'D4': 'C', 'D5': 'W', 'D2': 'M', 'D3': 'T', 'D1': 'F'}, False)
p1_38 = ({'A1': 'F', 'A3': 'S', 'A2': 'Z', 'A5': 'D', 'A4': 'H', 'C3': 'B', 'C2': 'G', 'C1': 'R', 'C5': 'W', 'C4': 'Y', 'N1': 'J', 'N2': 'N', 'N3': 'E', 'N4': 'I', 'N5': 'S', 'J4': 'V', 'J5': 'Di', 'J1': 'Do', 'J2': 'S', 'J3': 'P', 'D4': 'F', 'D5': 'W', 'D2': 'T', 'D3': 'C', 'D1': 'M'}, False)
p1_39 = ({'A1': 'Z', 'A3': 'H', 'A2': 'D', 'A5': 'F', 'A4': 'S', 'C3': 'R', 'C2': 'W', 'C1': 'Y', 'C5': 'B', 'C4': 'G', 'N1': 'J', 'N2': 'S', 'N3': 'N', 'N4': 'I', 'N5': 'E', 'J4': 'S', 'J5': 'Do', 'J1': 'Di', 'J2': 'V', 'J3': 'P', 'D4': 'M', 'D5': 'F', 'D2': 'W', 'D3': 'T', 'D1': 'C'}, False)
p1_40 = ({'A1': 'D', 'A3': 'F', 'A2': 'H', 'A5': 'Z', 'A4': 'S', 'C3': 'R', 'C2': 'W', 'C1': 'G', 'C5': 'Y', 'C4': 'B', 'N1': 'S', 'N2': 'I', 'N3': 'E', 'N4': 'J', 'N5': 'N', 'J4': 'Do', 'J5': 'V', 'J1': 'Di', 'J2': 'P', 'J3': 'S', 'D4': 'F', 'D5': 'C', 'D2': 'M', 'D3': 'T', 'D1': 'W'}, False)
p1_41 = ({'A1': 'F', 'A3': 'D', 'A2': 'Z', 'A5': 'S', 'A4': 'H', 'C3': 'B', 'C2': 'R', 'C1': 'W', 'C5': 'Y', 'C4': 'G', 'N1': 'I', 'N2': 'S', 'N3': 'N', 'N4': 'E', 'N5': 'J', 'J4': 'S', 'J5': 'V', 'J1': 'Di', 'J2': 'Do', 'J3': 'P', 'D4': 'C', 'D5': 'W', 'D2': 'F', 'D3': 'M', 'D1': 'T'}, False)
p1_42 = ({'A1': 'Z', 'A3': 'F', 'A2': 'S', 'A5': 'H', 'A4': 'D', 'C3': 'B', 'C2': 'G', 'C1': 'Y', 'C5': 'R', 'C4': 'W', 'N1': 'E', 'N2': 'I', 'N3': 'N', 'N4': 'J', 'N5': 'S', 'J4': 'P', 'J5': 'S', 'J1': 'Do', 'J2': 'V', 'J3': 'Di', 'D4': 'T', 'D5': 'C', 'D2': 'F', 'D3': 'W', 'D1': 'M'}, False)
p1_43 = ({'A1': 'F', 'A3': 'Z', 'A2': 'H', 'A5': 'S', 'A4': 'D', 'C3': 'Y', 'C2': 'G', 'C1': 'B', 'C5': 'R', 'C4': 'W', 'N1': 'S', 'N2': 'E', 'N3': 'N', 'N4': 'I', 'N5': 'J', 'J4': 'P', 'J5': 'Do', 'J1': 'V', 'J2': 'Di', 'J3': 'S', 'D4': 'T', 'D5': 'W', 'D2': 'F', 'D3': 'C', 'D1': 'M'}, False)
p1_44 = ({'A1': 'Z', 'A3': 'F', 'A2': 'D', 'A5': 'S', 'A4': 'H', 'C3': 'W', 'C2': 'G', 'C1': 'B', 'C5': 'R', 'C4': 'Y', 'N1': 'S', 'N2': 'N', 'N3': 'E', 'N4': 'I', 'N5': 'J', 'J4': 'Do', 'J5': 'S', 'J1': 'P', 'J2': 'V', 'J3': 'Di', 'D4': 'M', 'D5': 'C', 'D2': 'F', 'D3': 'T', 'D1': 'W'}, False)
p1_45 = ({'A1': 'F', 'A3': 'H', 'A2': 'Z', 'A5': 'D', 'A4': 'S', 'C3': 'R', 'C2': 'G', 'C1': 'Y', 'C5': 'B', 'C4': 'W', 'N1': 'N', 'N2': 'E', 'N3': 'S', 'N4': 'J', 'N5': 'I', 'J4': 'V', 'J5': 'Di', 'J1': 'Do', 'J2': 'S', 'J3': 'P', 'D4': 'M', 'D5': 'F', 'D2': 'C', 'D3': 'W', 'D1': 'T'}, False)
p1_46 = ({'A1': 'F', 'A3': 'H', 'A2': 'D', 'A5': 'S', 'A4': 'Z', 'C3': 'Y', 'C2': 'R', 'C1': 'B', 'C5': 'G', 'C4': 'W', 'N1': 'N', 'N2': 'I', 'N3': 'E', 'N4': 'J', 'N5': 'S', 'J4': 'S', 'J5': 'V', 'J1': 'Do', 'J2': 'P', 'J3': 'Di', 'D4': 'M', 'D5': 'C', 'D2': 'T', 'D3': 'W', 'D1': 'F'}, False)
p1_47 = ({'A1': 'S', 'A3': 'F', 'A2': 'D', 'A5': 'Z', 'A4': 'H', 'C3': 'R', 'C2': 'G', 'C1': 'B', 'C5': 'Y', 'C4': 'W', 'N1': 'E', 'N2': 'S', 'N3': 'I', 'N4': 'J', 'N5': 'N', 'J4': 'V', 'J5': 'Do', 'J1': 'S', 'J2': 'Di', 'J3': 'P', 'D4': 'W', 'D5': 'M', 'D2': 'C', 'D3': 'F', 'D1': 'T'}, False)
p1_48 = ({'A1': 'H', 'A3': 'S', 'A2': 'Z', 'A5': 'D', 'A4': 'F', 'C3': 'B', 'C2': 'Y', 'C1': 'W', 'C5': 'G', 'C4': 'R', 'N1': 'I', 'N2': 'J', 'N3': 'S', 'N4': 'E', 'N5': 'N', 'J4': 'S', 'J5': 'P', 'J1': 'Di', 'J2': 'V', 'J3': 'Do', 'D4': 'C', 'D5': 'T', 'D2': 'W', 'D3': 'M', 'D1': 'F'}, False)
p1_49 = ({'A1': 'D', 'A3': 'S', 'A2': 'H', 'A5': 'Z', 'A4': 'F', 'C3': 'R', 'C2': 'B', 'C1': 'Y', 'C5': 'W', 'C4': 'G', 'N1': 'E', 'N2': 'J', 'N3': 'S', 'N4': 'N', 'N5': 'I', 'J4': 'Do', 'J5': 'P', 'J1': 'S', 'J2': 'Di', 'J3': 'V', 'D4': 'F', 'D5': 'W', 'D2': 'M', 'D3': 'T', 'D1': 'C'}, False)


# p2 test cases
# test with your CSPBacktrackingSolver and the *unmodified* nQueensCSP function
# csp = nQueensCSP(n)
# solver = CSPBacktrackingSolver(csp)
# res = solver.solve()
# use isValid method on an *unmodified* nQueensCSP to validate
# Case 0: n=4
# Case 1: n=8
# Case 2: n=12
# Case 3: n=16


# p4 test cases; test case number is the suffix on the variable
# test with your marginalize, condition1, or condition2 as indicated in the variable name
# each test case is a tuple containing:
# for marginalize: (probabilities, index, reference_solution)
# for condition1/2: (probabilities, index, value, reference_solution)
# values are considered the same if they are close (can use numpy.isclose if you have numpy installed):
# the inequality is (math, not valid code): absolute(a - b) <= (1e-8 + 1e-5 * absolute(b))
# (this is necessary due to the nature of floating point values)
p4_marg_00 = ({(0, 1): 0.2, (1, 0): 0.3, (0, 0): 0.1, (1, 1): 0.4}, 0, {(0,): 0.4, (1,): 0.6000000000000001})
p4_marg_01 = ({(0, 1): 0.2, (1, 0): 0.3, (0, 0): 0.1, (1, 1): 0.4}, 1, {(0,): 0.30000000000000004, (1,): 0.7})
p4_marg_02 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 0, {(0, 1): 0.25, (1, 0): 0.29, (0, 0): 0.15000000000000002, (1, 1): 0.31})
p4_marg_03 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 1, {(0, 1): 0.4, (1, 0): 0.09, (0, 0): 0.35, (1, 1): 0.16})
p4_marg_04 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 2, {(0, 1): 0.55, (1, 0): 0.2, (0, 0): 0.2, (1, 1): 0.05})
p4_cond1_00 = ({(0, 1): 0.2, (1, 0): 0.3, (0, 0): 0.1, (1, 1): 0.4}, 0, 1, {(0,): 0.4285714285714286, (1,): 0.5714285714285715})
p4_cond1_01 = ({(0, 1): 0.2, (1, 0): 0.3, (0, 0): 0.1, (1, 1): 0.4}, 1, 1, {(0,): 0.3333333333333333, (1,): 0.6666666666666666})
p4_cond1_02 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 0, 1, {(0, 1): 0.6, (1, 0): 0.16, (0, 0): 0.2, (1, 1): 0.04})
p4_cond1_03 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 1, 1, {(0, 1): 0.4999999999999999, (1, 0): 0.06666666666666665, (0, 0): 0.41666666666666663, (1, 1): 0.016666666666666663})
p4_cond1_04 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 2, 1, {(0, 1): 0.5357142857142857, (1, 0): 0.26785714285714285, (0, 0): 0.17857142857142858, (1, 1): 0.017857142857142856})
p4_cond2_00 = ({(0, 1): 0.2, (1, 0): 0.3, (0, 0): 0.1, (1, 1): 0.4}, 0, 1, {(0,): 0.4285714285714286, (1,): 0.5714285714285715})
p4_cond2_01 = ({(0, 1): 0.2, (1, 0): 0.3, (0, 0): 0.1, (1, 1): 0.4}, 1, 1, {(0,): 0.3333333333333333, (1,): 0.6666666666666666})
p4_cond2_02 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 0, 1, {(0, 1): 0.6, (1, 0): 0.16, (0, 0): 0.2, (1, 1): 0.04})
p4_cond2_03 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 1, 1, {(0, 1): 0.5, (1, 0): 0.06666666666666667, (0, 0): 0.4166666666666667, (1, 1): 0.016666666666666666})
p4_cond2_04 = ({(0, 1, 1): 0.3, (0, 0, 0): 0.1, (1, 1, 0): 0.04, (1, 0, 0): 0.05, (0, 1, 0): 0.25, (0, 0, 1): 0.1, (1, 1, 1): 0.01, (1, 0, 1): 0.15}, 2, 1, {(0, 1): 0.5357142857142857, (1, 0): 0.26785714285714285, (0, 0): 0.1785714285714286, (1, 1): 0.01785714285714286})