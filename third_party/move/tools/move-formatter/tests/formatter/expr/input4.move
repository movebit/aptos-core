script {
fun main() {  
    let y: u64 = 100; // Define an unsigned 64-bit integer variable y and assign it a value of 100  
    let /*comment*/z/*comment*/ = if/*comment*/ (/*comment*/y <= /*comment*/10/*comment*/) { // If y is less than or equal to 10  
        y = y + 1; // Increment y by 1  
    }/*comment*/ else /*comment*/{  
        y = 10; // Otherwise, set y to 10  
    };  
}
}
