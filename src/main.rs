//! current version is basically just https://en.wikipedia.org/wiki/Brainfuck

use clap::Parser;
use std::{collections::BTreeMap, path::PathBuf};

macro_rules! dprint {
    ($($args:tt)*) => {
        #[cfg(debug_assertions)]
        print!($($args)*);
    };
}
macro_rules! dprintln {
    ($($args:tt)*) => {
        #[cfg(debug_assertions)]
        println!($($args)*);
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Instruction {
    /// `>` -- Increment the data pointer by one
    /// (to point to the next cell to the right).
    Next = b'>' as isize,
    /// `<` -- Decrement the data pointer by one
    /// (to point to the next cell to the left).
    Prev = b'<' as isize,
    /// `+` -- Increment the byte at the data pointer by one.
    Incr = b'+' as isize,
    /// `-` -- Decrement the byte at the data pointer by one.
    Decr = b'-' as isize,
    /// `.` -- Output the byte at the data pointer.
    Give = b'.' as isize,
    /// `,` -- Accept one byte of input, storing its value in the byte at the data pointer.
    Take = b',' as isize,
    /// `[` -- If the byte at the data pointer is zero,
    /// then instead of moving the instruction pointer forward to the next command,
    /// jump it forward to the command after the matching `]` command.
    Fore = b'[' as isize,
    /// `]` -- If the byte at the data pointer is nonzero,
    /// then instead of moving the instruction pointer forward to the next command,
    /// jump it back to the command after the matching `[` command.
    Back = b']' as isize,
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        char::from(*self as u8).fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct Instructions<I, F = fn(<I as Iterator>::Item) -> Option<Instruction>> {
    iter: std::iter::FilterMap<I, F>,
}

impl<I: Iterator, F: FnMut(I::Item) -> Option<Instruction>> Iterator for Instructions<I, F> {
    type Item = Instruction;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I: DoubleEndedIterator, F: FnMut(I::Item) -> Option<Instruction>> DoubleEndedIterator
    for Instructions<I, F>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<I, F> ExactSizeIterator for Instructions<I, F>
where
    Self: Iterator,
    std::iter::FilterMap<I, F>: Iterator + Clone,
{
    #[inline]
    fn len(&self) -> usize {
        self.iter.clone().count()
    }
}

impl<I: std::iter::FusedIterator, F> std::iter::FusedIterator for Instructions<I, F> where
    Self: Iterator
{
}

impl TryFrom<char> for Instruction {
    type Error = ();

    #[inline]
    fn try_from(value: char) -> Result<Self, Self::Error> {
        Self::from_char(value).ok_or(())
    }
}

impl TryFrom<u8> for Instruction {
    type Error = ();

    #[inline]
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_byte(value).ok_or(())
    }
}

impl Instruction {
    #[inline]
    pub const fn from_char(ch: char) -> Option<Self> {
        match ch {
            '>' => Some(Self::Next),
            '<' => Some(Self::Prev),
            '+' => Some(Self::Incr),
            '-' => Some(Self::Decr),
            '.' => Some(Self::Give),
            ',' => Some(Self::Take),
            '[' => Some(Self::Fore),
            ']' => Some(Self::Back),
            _ => None,
        }
    }
    #[inline]
    pub const fn from_byte(ch: u8) -> Option<Self> {
        match ch {
            b'>' => Some(Self::Next),
            b'<' => Some(Self::Prev),
            b'+' => Some(Self::Incr),
            b'-' => Some(Self::Decr),
            b'.' => Some(Self::Give),
            b',' => Some(Self::Take),
            b'[' => Some(Self::Fore),
            b']' => Some(Self::Back),
            _ => None,
        }
    }

    #[inline]
    pub fn converter<I: IntoIterator>(s: I) -> Instructions<I::IntoIter>
    where
        I::Item: TryInto<Self>,
    {
        Instructions {
            iter: s.into_iter().filter_map(|ch| ch.try_into().ok()),
        }
    }

    #[inline]
    pub fn parser(s: &str) -> Instructions<std::str::Chars<'_>> {
        Self::converter(s.chars())
    }

    #[inline]
    pub fn vec_from_str(s: &str) -> Vec<Self> {
        let iter = Self::parser(s);
        let mut v = Vec::with_capacity(iter.len());
        v.extend(iter);
        v
    }

    #[inline]
    pub fn vec_from_bytes(s: &[u8]) -> Vec<Self> {
        let iter = Self::converter(s.iter().copied());
        let mut v = Vec::with_capacity(iter.len());
        v.extend(iter);
        v
    }
}

#[derive(Debug)]
pub enum RuntimeError {
    LineOutOfRange,
    DataPtrOutOfRange,
    Input(std::io::Error),
    Output(std::io::Error),
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LineOutOfRange => "line pointer overflowed or exceeds program length",
            Self::DataPtrOutOfRange => "data pointer exceeds ram size",
            Self::Input(_) => "input error",
            Self::Output(_) => "output error",
        }
        .fmt(f)
    }
}

impl std::error::Error for RuntimeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Input(e) | Self::Output(e) => Some(e),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CompileError {
    UnclosedLoop,
    UnopenedLoop,
    Overflow,
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnclosedLoop => "a `[` is missing its corresponding `]`",
            Self::UnopenedLoop => "a `]` is missing its corresponding `[`",
            Self::Overflow => {
                "code is too long and would invalidly loop back to the start if it were to run"
            }
        }
        .fmt(f)
    }
}

impl std::error::Error for CompileError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct Program<'a> {
    code: &'a [Instruction],
    loops: BTreeMap<usize, usize>,
}

impl<'a> Program<'a> {
    pub fn compile(code: &'a [Instruction]) -> Result<Self, CompileError> {
        if code.len() == usize::MAX {
            return Err(CompileError::Overflow);
        }
        let mut loops = BTreeMap::new();
        let mut stack = Vec::with_capacity(
            code.iter()
                .filter(|x| matches!(x, Instruction::Fore))
                .count(),
        );
        for (i, item) in code.iter().enumerate() {
            match item {
                Instruction::Fore => {
                    stack.push(i);
                }
                Instruction::Back => {
                    let j = stack.pop().ok_or(CompileError::UnopenedLoop)?;
                    loops.insert(i, j);
                    loops.insert(j, i);
                    // not incrementing destination because that will be handled by the end-of-line jump
                }
                _ => {}
            }
        }
        if stack.is_empty() {
            Ok(Self { code, loops })
        } else {
            Err(CompileError::UnclosedLoop)
        }
    }
}

#[derive(Debug)]
pub struct Environment<'a, 'b, 'c, I, O> {
    data: &'a mut [u8],
    prgm: &'b Program<'c>,
    head: usize,
    line: usize,
    istream: I,
    ostream: O,
}

impl<'a, 'b, 'c, I, O> Environment<'a, 'b, 'c, I, O> {
    pub const fn new(data: &'a mut [u8], prgm: &'b Program<'c>, istream: I, ostream: O) -> Self {
        Self {
            data,
            prgm,
            head: 0,
            line: 0,
            istream,
            ostream,
        }
    }
}

impl<'a, 'b, 'c, I: std::io::Read, O: std::io::Write> Environment<'a, 'b, 'c, I, O> {
    #[inline]
    fn at_head(&self) -> Result<u8, RuntimeError> {
        self.data
            .get(self.head)
            .copied()
            .ok_or(RuntimeError::DataPtrOutOfRange)
    }
    #[inline]
    fn at_head_mut(&mut self) -> Result<&mut u8, RuntimeError> {
        self.data
            .get_mut(self.head)
            .ok_or(RuntimeError::DataPtrOutOfRange)
    }

    pub fn step(&mut self) -> Result<(), RuntimeError> {
        dprint!("line {}:", self.line);
        let item = self
            .prgm
            .code
            .get(self.line)
            .ok_or(RuntimeError::LineOutOfRange)?;
        dprint!(" {item}");
        match item {
            Instruction::Next => {
                dprint!("  &[{}] ->", self.head);
                self.head = self.head.wrapping_add(1);
                dprintln!(" &[{}]", self.head);
            }
            Instruction::Prev => {
                dprint!("  &[{}] ->", self.head);
                self.head = self.head.wrapping_sub(1);
                dprintln!(" &[{}]", self.head);
            }

            Instruction::Incr => {
                dprint!("  [{}]", self.head);
                let byte = self.at_head_mut()?;
                dprint!(" {byte} ->");
                *byte = (*byte).wrapping_add(1);
                dprintln!(" {byte}");
            }
            Instruction::Decr => {
                dprint!("  [{}]", self.head);
                let byte = self.at_head_mut()?;
                dprint!(" {byte} ->");
                *byte = (*byte).wrapping_sub(1);
                dprintln!(" {byte}");
            }

            Instruction::Give => {
                dprint!("  [out] << [{}]", self.head);
                let byte = self.at_head()?;
                dprintln!(" {byte}");
                self.ostream
                    .write_all(std::slice::from_ref(&byte))
                    .map_err(RuntimeError::Output)?;
            }
            Instruction::Take => {
                let mut byte = 0;
                self.istream
                    .read_exact(std::slice::from_mut(&mut byte))
                    .map_err(RuntimeError::Input)?;
                dprint!("  [in] {byte} >>");
                dprint!(" [{}]", self.head);
                let dest = self.at_head_mut()?;
                dprint!(" {dest} ->");
                *dest = byte;
                dprintln!(" {dest}");
            }

            Instruction::Fore => {
                dprint!("  [{}]", self.head);
                let byte = self.at_head()?;
                dprint!(" {byte}");
                if byte == 0 {
                    dprint!(" == 0 : [[{}]] ->", self.line);
                    self.line = self
                        .prgm
                        .loops
                        .get(&self.line)
                        .copied()
                        .expect("should have been caught by Program::compile");
                    dprintln!(" [[{}]]", self.line);
                } else {
                    dprintln!(" != 0");
                }
            }
            Instruction::Back => {
                dprint!("  [{}]", self.head);
                let byte = self.at_head()?;
                dprint!(" {byte}");
                if byte != 0 {
                    dprint!(" != 0 : [[{}]] ->", self.line);
                    self.line = self
                        .prgm
                        .loops
                        .get(&self.line)
                        .copied()
                        .expect("should have been caught by Program::compile");
                    dprintln!(" [[{}]]", self.line);
                } else {
                    dprintln!(" == 0");
                }
            }
        }

        Ok(())
    }

    #[inline]
    pub fn run(&mut self) -> Result<(), RuntimeError> {
        loop {
            if let Err(e) = self.step() {
                break Err(e);
            }
            match self.line.checked_add(1) {
                Some(line) => self.line = line,
                None => break Err(RuntimeError::LineOutOfRange),
            }
            if self.line == self.prgm.code.len() {
                break Ok(());
            }
        }
    }
}

#[derive(Debug, Parser)]
pub struct Cli {
    /// How much memory to give the application
    #[arg(short, long, default_value = "2048")]
    mem: usize,

    /// Path to the code file
    path: PathBuf,
}

fn main() -> Result<(), ()> {
    let Cli { mem, path } = Cli::parse();
    let code = Instruction::vec_from_str(
        &std::fs::read_to_string(path).expect("failed to read code from file"),
    );

    #[cfg(debug_assertions)]
    {
        for item in &code {
            dprint!("{item}");
        }
        dprintln!();
        dprintln!("len: {}", code.len());
    }

    match Program::compile(&code) {
        Err(e) => {
            eprintln!("compile error: {e}");
            Err(())
        }
        Ok(prgm) => {
            let mut memory = vec![0u8; mem];
            let mut env = Environment::new(&mut memory, &prgm, std::io::stdin(), std::io::stdout());
            match env.run() {
                Ok(()) => Ok(()),
                Err(e) => {
                    dprintln!(" ERR");
                    eprintln!("runtime error: {e}");
                    Err(())
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let code = Instruction::vec_from_str(r#"[->+<]"#);
        let prgm = Program::compile(&code).unwrap();
        for (a, b) in [(4, 7), (9, 2), (0, 23), (255, 5)] {
            let mut ram = [a, b];
            Environment::new(&mut ram, &prgm, &[][..], &mut [][..])
                .run()
                .unwrap();
            assert_eq!(ram, [0, a.wrapping_add(b)]);
        }
    }

    #[test]
    fn test_seven() {
        let code = Instruction::vec_from_str(
            r#"
++       Cell c0 = 2
> +++++  Cell c1 = 5

[        Start your loops with your cell pointer on the loop counter (c1 in our case)
< +      Add 1 to c0
> -      Subtract 1 from c1
]        End your loops with the cell pointer on the loop counter

At this point our program has added 5 to 2 leaving 7 in c0 and 0 in c1
but we cannot output this value to the terminal since it is not ASCII encoded

To display the ASCII character "7" we must add 48 to the value 7
We use a loop to compute 48 = 6 * 8

++++ ++++  c1 = 8 and this will be our loop counter again
[
< +++ +++  Add 6 to c0
> -        Subtract 1 from c1
]
< .        Print out c0 which has the value 55 which translates to "7"!
        "#,
        );
        let prgm = Program::compile(&code).unwrap();
        let mut output = [0; 1];
        Environment::new(&mut [0; 2], &prgm, &[][..], &mut output[..])
            .run()
            .unwrap();
        assert_eq!(&output, b"7");
    }

    #[test]
    fn test_hello_world() {
        let code = Instruction::vec_from_str(
            r#"
[ This program prints "Hello World!" and a newline to the screen; its
  length is 106 active command characters. [It is not the shortest.]

  This loop is an "initial comment loop", a simple way of adding a comment
  to a BF program such that you don't have to worry about any command
  characters. Any ".", ",", "+", "-", "<" and ">" characters are simply
  ignored, the "[" and "]" characters just have to be balanced. This
  loop and the commands it contains are ignored because the current cell
  defaults to a value of 0; the 0 value causes this loop to be skipped.
]
++++++++                Set Cell #0 to 8
[
    >++++               Add 4 to Cell #1; this will always set Cell #1 to 4
    [                   as the cell will be cleared by the loop
        >++             Add 2 to Cell #2
        >+++            Add 3 to Cell #3
        >+++            Add 3 to Cell #4
        >+              Add 1 to Cell #5
        <<<<-           Decrement the loop counter in Cell #1
    ]                   Loop until Cell #1 is zero; number of iterations is 4
    >+                  Add 1 to Cell #2
    >+                  Add 1 to Cell #3
    >-                  Subtract 1 from Cell #4
    >>+                 Add 1 to Cell #6
    [<]                 Move back to the first zero cell you find; this will
                        be Cell #1 which was cleared by the previous loop
    <-                  Decrement the loop Counter in Cell #0
]                       Loop until Cell #0 is zero; number of iterations is 8

The result of this is:
Cell no :   0   1   2   3   4   5   6
Contents:   0   0  72 104  88  32   8
Pointer :   ^

>>.                     Cell #2 has value 72 which is 'H'
>---.                   Subtract 3 from Cell #3 to get 101 which is 'e'
+++++++..+++.           Likewise for 'llo' from Cell #3
>>.                     Cell #5 is 32 for the space
<-.                     Subtract 1 from Cell #4 for 87 to give a 'W'
<.                      Cell #3 was set to 'o' from the end of 'Hello'
+++.------.--------.    Cell #3 for 'rl' and 'd'
>>+.                    Add 1 to Cell #5 gives us an exclamation point
>++.                    And finally a newline from Cell #6
        "#,
        );
        let prgm = Program::compile(&code).unwrap();
        let mut output = [0; 13];
        Environment::new(&mut [0; 128][..], &prgm, &[][..], &mut output[..])
            .run()
            .unwrap();
        assert_eq!(&output, b"Hello World!\n");
    }
}
