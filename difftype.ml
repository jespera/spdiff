type 'a diff = 
    | ID of 'a 
    | ADD of 'a 
    | RM of 'a 
    | UP of 'a * 'a
    | SEQ of 'a diff * 'a diff
