# Approaching TLA+ from the CLI

This doc describes my attempt (in 2019-12) to ramp up on TLA+ without reliance
on the TLA+ IDE. This was inspired by [this
tweet](https://twitter.com/hillelogram/status/1207874445823623168).

# My background and expectations

I am a Google software engineer and Mathematics PhD. I have professional
experience working with dozens of languages and frameworks, and at the time of
this writing most my professional work is in Java or Python. My PhD was in the
theory of computer science. There was a time in my life when I used IDEs
primarily, have extensively used tools like Eclipse, PyCharm, Jupyter, etc.,
but today I do all my work in vim.

I like my tools to be straightforward and easy to separate. For example, when
creating a new Python project I work in an isolated directory, and create a
separate virtual environment and requirements file dedicated to the project. I
write a math blog where each topic receives its own Github repository (over a
hundred to date), and it's important that I can remove these from my machine
and recreate them from scratch at any time.

I also like to have my build, test, and run functionality accessible on the
command line, and for those tools to be easily inspectable. I.e., where do they
expect files to be, what naming conventions do they enforce, and what files do
they create and where? Can I specify it myself via flags? What is the meaning
of each tool's output, so that when things go wrong I can interpret the error
messages and learn where the problem is and how to fix it? Do these tools
follow the same sorts of expectations that allow me to plug in other tools (via
shell piping, for example)?

All of these issues point to a single principle that guides me when it comes to
tools and software: self-reliance. My tools should limit, to the greatest
extent possible, forcing my reliance on a particular method of operating with
it. If I can't understand the organization of a system broadly, or if I can't
easily drill down on a particular component when it is causing problems, then
it's a guaranteed future problem.

Though it cannot always be avoided, I enjoy using tools that empower me to be
more self-reliant over tools that violate it.

# Setting up

```
mkdir ~/prototypes/tla
cd ~/prototypes/tla
git it   # alias for !git init && git commit -m "root" --allow-empty
git remote add origin git@github.com:j2kun/tla_cli.git
git push -u origin master
```

I expect each significant TLA+ project to get its own git repository.

# Hello Lamport

Now I need to find a "hello world" specification to write, build, and model
check. Here is where things start to diverge. I went through three different
sources. First, Leslie Lamport's video tutorial, which I'll put into a
subdirectory of this repository called `hello_lamport`.


