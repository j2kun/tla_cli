# Approaching TLA+ from the CLI

This doc describes my attempt (in 2019-12) to ramp up on TLA+ without reliance
on the TLA+ IDE. This was inspired by [this
tweet](https://twitter.com/hillelogram/status/1207874445823623168).

- [Setting up](#setting-up)
- [Hello Lamport](#hello-lamport)
- [Looking around](#looking-around)
- [Hello UI](#hello-ui)
- [What have I learned?](#what-have-i-learned-)

# Setting up

```
mkdir ~/prototypes/tla
cd ~/prototypes/tla
git it   # alias for !git init && git commit -m "root" --allow-empty
git remote add origin git@github.com:j2kun/tla_cli.git
git push -u origin main
```

# Hello Lamport

I need a "hello world" specification. I went through three different sources.
First, Leslie Lamport's video tutorial, which I'll put into a subdirectory of
this repository called `hello_lamport`.

Lamport's [video course](http://lamport.azurewebsites.net/video/videos.html)
(whose style I adore) has one "hello world", while his book [Specifying
Systems](https://lamport.azurewebsites.net/tla/book.html) has a different
"hello world" based on an hour clock. From the video lecture (end of lecture
2), the "add one" specification:

```tla
--------------- MODULE SimpleProgram ---------------
EXTENDS Integers
VARIABLES i, pc
Init == (pc = "start") /\ (i = 0)
Next == \/ /\ pc = "start"
           /\ i’ \in 0..1000
           /\ pc’ = "middle"
        \/ /\ pc = "middle"
           /\ i’ = i + 1
           /\ pc’ = "done"
====================================================
```

And from the book, a simple hour clock.

```tla
---------------------- MODULE HourClock ----------------------
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM HC => []HCini
==============================================================
```

I saved these to the files `add_one.tla` and `hour_clock.tla`, respectively.

I will avoid commenting on the syntax while we focus on getting one of these
specifications to compile, run, and model check. Spoiler: I do not succeed. At
this point, it's not clear which of these is even complete. For instance, one
has a "theorem" block and one does not. I should be able to check for a
deadlock at least.

Specifying Systems Chapter 2 provides no explanation for how to compile or run
the model checker on the simple clock, and the video lectures walk you through
using the user interface.

On the TLA+ website I find the "TLA Hyperbook," which is composed of a bunch of
pdf files with hyperlinks between them. The hello world example in this book is
a "one bit clock", but the book again only tells you what buttons to click in
the UI to parse and run the model checker.

Then there is [this
pdf](https://lamport.azurewebsites.net/tla/current-tools.pdf) explaining the
"current versions of the tools" as of 2018. The pdf contains four sections, for
tools called `SANY`, `TLC`, `TLALATEX`, and `PlusCal`.  The section on `SANY`
simply says, "The current release of SANY has no known limitations." Well that
was useless. The rest of the file appears to be relese notes showing what has
changed about the command line tools (so there are CLI tools!) since Specifying
Systems was published.

Finally I find [this
page](https://lamport.azurewebsites.net/tla/standalone-tools.html) for running
the TLA+ tools "standalone." There is a link to a [Github release
page.](https://github.com/tlaplus/tlaplus/releases/tag/v1.6.0) Now we're
getting somewhere. The instructions on that page ask you to download a zip
containing a JAR file (Java archive), set up a CLASSPATH to point to it, and
then run the scripts via the Java command:

```
java tlc2.TLC
java tla2sany.SANY
java pcal.trans
java tla2tex.TLA
```

Knowing Java well enough, I can use the `-cp` flag on the `java` CLI to set a
classpath per invocation, and I don't want to modify my system (I will be
guaranteed to forget what I did). So installing the CLI tools (finally) is as
simple as

```bash
wget https://github.com/tlaplus/tlaplus/releases/download/v1.6.0/tla2tools.jar
java -cp tla2tools.jar tlc2.TLC
```

I get:

```
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
Error: Error: Missing input TLA+ module.
Usage: java tlc2.TLC [-option] inputfile
```

Excellent! Except---I still don't know what the hell these four commands do.
`tla2tex` is self-evident, but SANY is still a mystery (I guess it's a parser?)
And tlc2.TLC is presumably the model checker. `pcal.trans` is who knows what
(Googling shows it's a language that compiles to TLA, somehow through writing
code in comment blocks of normal TLA files??).

Some more false starts:

```
$ java -cp tla2tools.jar tlc2.TLC --help
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
Error: Error: unrecognized option: --help
Usage: java tlc2.TLC [-option] inputfile
```

Remembering (or realizing now) that TLC is written on top of Java, I guess the
long switches might be single-hyphen.

```
$ java -cp tla2tools.jar tlc2.TLC -help
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
The model checker (TLC) provides the functionalities of model
checking or simulation of TLA+ specifications. The syntax for this command is:

java tlc2.TLC [GENERAL-SWITCHES] [MODE-SWITCHES] SPEC

where SPEC is the name of the specification's root module
and the optional GENERAL-SWITCHES are:
-checkpoint num: interval between check point (in minutes)
	Defaults 30 if not provided.
-cleanup: clean up the states directory
-config file: provide the config file.
	Defaults to SPEC.cfg if not provided
...

By default, TLC starts in the model checking mode using breadth-first
approach for the state space exploration. This can be changed using
the MODE-SWITCHES. In contrast to the GENERAL-SWITCHES these can be used
if applied in certain combinations only:

{[-dfid num][ -view]|-simulate[ -depth num][ -aril num][ -seed num]}

-modelcheck: run in model checking mode using breadth-first approach for the
	state space exploration (default)
...
```

Great! Let's run it on the `add_one` spec I wrote.

```bash
$ java -cp tla2tools.jar tlc2.TLC hello_lamport/add_one.tla
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
Warning: Please run the Java VM which executes TLC with a throughput optimized garbage collector by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 101 and seed 6345125587550240554 with 1 worker on 4 cores with 2048MB heap and 64MB offheap memory [pid: 97903] (Mac OS X 10.14.6 x86_64, Oracle Corporation 10.0.1 x86_64, MSBDiskFPSet, DiskStateQueue).
Error: TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a tlc2.tool.ConfigFileException
: TLC encountered the following error when trying to read the configuration file hello_lamport/add_one.cfg:
File not found.
Finished in 00s at (2019-12-23 09:54:40)
```

OK, hidden in all the junk it seems it's looking for a config file that I
didn't know needed to exist (it's not mentioned in the UI instructions of any
of the aforementioned resources). What should be in this config file? What is
the format?

Googling around shows [this page from the UI
designers](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/executing-tlc.html#MC)
that doesn't help. Then this [github
issue](https://github.com/tlaplus/Examples/issues/6) that says, "Let the UI do
it for you." One [helpful
comment](https://github.com/tlaplus/Examples/issues/6#issuecomment-415307340)
explains the reason for the config file's existence: the model spec is
"infinite-state" and the onfig file specifies the parameters of a particular
instantiation of the model to check.

Then this [google group
thread](https://groups.google.com/forum/#!topic/tlaplus/IBpkSU_rgng) that
points to Chapter 14 of Specifying Systems. Chapter 14 starts by saying it's
describing tools that are out of date. Then it describes some very brief
information about what can go in a config file.

![Screenshot from Specifying Systems](specifying_systems_cfg.png)

Here it seems to say that the syntax should look like this

```
SPECIFICATION foo
```

Or by manually putting in an init and next state (if there's not a liveness
condition in the spec, which, again, because this is a hello world, I dont
understand). That alternative might look like

```
INIT foo
NEXT bar
```

Luckily add_one does look like that, so my cfg, now in `add_one.cfg` is

```
INIT Init
NEXT Next
```

Running it:

```bash
$ java -cp tla2tools.jar tlc2.TLC hello_lamport/add_one.tla
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
Warning: Please run the Java VM which executes TLC with a throughput optimized garbage collector by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 96 and seed -6157446468698750503 with 1 worker on 4 cores with 2048MB heap and 64MB offheap memory [pid: 99881] (Mac OS X 10.14.6 x86_64, Oracle Corporation 10.0.1 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /Users/jeremy/prototypes/tla/hello_lamport/add_one.tla
Lexical error at line 6, column 16.  Encountered: "\u2019" (8217), after : ""

Fatal errors while parsing TLA+ spec in file hello_lamport/add_one

tla2sany.semantic.AbortException
*** Abort messages: 1

In module add_one

Could not parse module add_one from file hello_lamport/add_one.tla

Starting... (2019-12-23 10:24:21)
Error: Parsing or semantic analysis failed.
Finished in 01s at (2019-12-23 10:24:21)
```

The `u2019` unicode issue turns out to be because copying the model spec from
Lamport's website retains the curliness of the quote, instead of using ascii
quotes. Fine, easy fix, though it's not clear how the inventor of LaTeX messed
up his verbatim environment :). The bigger problem seems to be that it can't
parse the contents. After a while I realize that the name of the module needs
to be identical with the name of the file. It goes unnoticed and unremarked in
the literature because the UI forces it. (It also seems to be an unnecessary
restriction, but so be it.)

Round three:

```bash
$ java -cp tla2tools.jar tlc2.TLC hello_lamport/add_one.tla
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
Warning: Please run the Java VM which executes TLC with a throughput optimized garbage collector by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 48 and seed -1739863346183740757 with 1 worker on 4 cores with 2048MB heap and 64MB offheap memory [pid: 1018] (Mac OS X 10.14.6 x86_64, Oracle Corporation 10.0.1 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /Users/jeremy/prototypes/tla/hello_lamport/add_one.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/Integers.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/Naturals.tla
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module add_one
Starting... (2019-12-23 10:28:05)
Error: TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a java.lang.NullPointerException
java.lang.NullPointerException
	at tlc2.tool.impl.SpecProcessor.processSpec(SpecProcessor.java:346)
	at tlc2.tool.impl.SpecProcessor.<init>(SpecProcessor.java:157)
	at tlc2.tool.impl.Spec.<init>(Spec.java:121)
	at tlc2.tool.impl.Tool.<init>(Tool.java:126)
	at tlc2.tool.impl.Tool.<init>(Tool.java:121)
	at tlc2.tool.impl.Tool.<init>(Tool.java:116)
	at tlc2.TLC.process(TLC.java:930)
	at tlc2.TLC.main(TLC.java:247)

Finished in 01s at (2019-12-23 10:28:05)
```

I would have expected, due to the CLI help text below, that if I run the model
checker tool with no flags it by default checks for a deadlock. Except, that the
flag looks like a boolean switch that turns _off_ deadlock (weird, might be a
typo), but trying to run with that flag seems to have no effect anyway.

```
-deadlock: do not check for deadlock.
	Defaults to check deadlock if not specified
```

Now I really don't know what the hell is going on. It looks like I'll have to
dig into the source code to determine what's tripping it up.  This is
especially strange because running `SANY`, which I expect to be some kind of
parser, on the same file, reports no errors.

```bash
$ java -cp tla2tools.jar tla2sany.SANY hello_lamport/add_one.tla

****** SANY2 Version 2.1 created 24 February 2014

Parsing file /Users/jeremy/prototypes/tla/hello_lamport/add_one.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/Integers.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/Naturals.tla
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module add_one
```

Looking at `hour_clock.tla`, maybe because I don't have a `THEOREM` TLC doesn't
know what to do? But I'm not sure how to add a theorem block to the config
file. It's not an INVARIANT, PROPERTY, or CONSTRAINT, none of which I
understand yet, but those are the ones that Chapter 14 of Specifying Systems
says can go in a config file. Same NPE happens when I try random other flags
and stuff.

I also noticed that the model checker creates a directory like
`states/19-12-23-10-24-19` (apparently referencing the time) every time it's
run, and it doesn't clean up after itself. So I'll have to add `states/` to my
`.gitignore`.

# Looking around

At this point I randomly search the internet for resources. That turned up a
Medium
[article](https://medium.com/@bellmar/introduction-to-tla-model-checking-in-the-command-line-c6871700a6a2)
by Marianne Bellotti, who seems to agree with me that the UI is not ideal and
has a workaround to use CLI tools. This only repeats what I already figured
out, that it's a Java application you can wrap with some default flags and
bashisms (copied
[here](https://github.com/j2kun/tla_scratchwork/blob/master/scripts/tlc) to its
own script).

Then I find myself reading through the TLA Toolbox developers Github issues
(like [this one](https://github.com/tlaplus/tlaplus/issues/140)) and I learn
that the project is just as confusing for everyone else as it is for me. It's
not organized well to use with version control, people aren't sure what files
to keep and what to ditch, and there is something called a `.launch` file,
which is apparently owned by the UI.  Also apparently the codebase is somewhat
coupled (or used to be coupled) with the Eclipse IDE it was written in, which
is a red flag. This is all frustrating (though I did learn that [elasticsearch
uses TLA](https://github.com/elastic/elasticsearch-formal-models), cool!), and
I wonder why they can't just make the TLA tools simpler rather than add layers
on top of it reacting to dev confusion. I don't believe that the TLC system is
so complex from an organizational standpoint that this can't be done.

# Hello UI

Now I attempt to use the UI for the same problem, putting this code in
`hello_ui` for posterity. The UI takes my `add_one` and creates
`add_one.toolbox/add_one_model/` which contains `MC.tla` and `MC.cfg`.  The
former apparently just extends from my existing spec, and the latter looks just
like my cfg file I made by hand, modulo whitespace. This doesn't help my
confusion, though I can run the model checker in the UI. Maybe `MC` is a
reserved word that needs to be there? Some other places on the internet seem to
hard code that name. Or maybe I just didn't pass the right CLI flags.

The UI version also creates a whole bunch of random files like

```
.
├── add_one___add_one_model.launch
├── add_one___add_one_model_SnapShot_1573965349650.launch
├── add_one___add_one_model_SnapShot_1573965431149.launch
├── add_one_model
│   ├── MC.cfg
│   ├── MC.out
│   ├── MC.tla
│   ├── MC_TE.out
│   └── add_one.tla
├── add_one_model_SnapShot_1573965349650
│   ├── MC.cfg
│   ├── MC.out
│   ├── MC.tla
│   ├── MC_TE.out
│   └── add_one.tla
└── add_one_model_SnapShot_1573965431149
    ├── MC.cfg
    ├── MC.out
    ├── MC.tla
    ├── MC_TE.out
    └── add_one.tla
```

I'm not sure of the use of this being turned on by default, but OK. Just beef
up my `.gitignore`. It's also not clear what of the UI-generated stuff is
important to TLC and what is UI-specific. Does the TLC model checker need these
snapshot files and `_TE` files? From the github thread above it's clear the
`.launch` thing is UI specific, but if I hadn't stumbled on that I wouldn't
have known to ignore it.

The content of the launch file looks like

```
<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<launchConfiguration type="org.lamport.tla.toolbox.tool.tlc.modelCheck">
    <stringAttribute key="configurationName" value="add_one_model"/>
    <intAttribute key="distributedFPSetCount" value="0"/>
    <stringAttribute key="distributedNetworkInterface" value="192.168.0.106"/>
    <intAttribute key="distributedNodesCount" value="1"/>
    <stringAttribute key="distributedTLC" value="off"/>
    <intAttribute key="fpIndex" value="116"/>
    <intAttribute key="maxHeapSize" value="25"/>
    <stringAttribute key="modelBehaviorInit" value="Init"/>
    <stringAttribute key="modelBehaviorNext" value="Next"/>
    <stringAttribute key="modelBehaviorSpec" value=""/>
    <intAttribute key="modelBehaviorSpecType" value="2"/>
    <stringAttribute key="modelBehaviorVars" value="i, program_counter"/>
    <stringAttribute key="modelComments" value=""/>
    <booleanAttribute key="modelCorrectnessCheckDeadlock" value="false"/>
    <listAttribute key="modelCorrectnessInvariants"/>
    <listAttribute key="modelCorrectnessProperties"/>
    <stringAttribute key="modelExpressionEval" value=""/>
    <listAttribute key="modelParameterConstants"/>
    <intAttribute key="numberOfWorkers" value="2"/>
    <stringAttribute key="result.mail.address" value=""/>
    <stringAttribute key="specName" value="add_one"/>
    <stringAttribute key="tlcResourcesProfile" value="local custom"/>
</launchConfiguration>
```

Based on the github issue talk, I'd expect these to be CLI flags. However, they
seem to be unrelated to the actual TLC CLI.

Run the TLC CLI on the model spec generated by the UI also does not work.

```bash
$ java -cp tla2tools.jar tlc2.TLC hello_ui/add_one.toolbox/add_one_model/MC
TLC2 Version 2.14 of 10 July 2019 (rev: 0cae24f)
Warning: Please run the Java VM which executes TLC with a throughput optimized garbage collector by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 80 and seed -7041069318716578190 with 1 worker on 4 cores with 2048MB heap and 64MB offheap memory [pid: 12680] (Mac OS X 10.14.6 x86_64, Oracle Corporation 10.0.1 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /Users/jeremy/prototypes/tla/hello_ui/add_one.toolbox/add_one_model/MC.tla
Parsing file /Users/jeremy/prototypes/tla/hello_ui/add_one.toolbox/add_one_model/add_one.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/TLC.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/Integers.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/Naturals.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/Sequences.tla
Parsing file /private/var/folders/k2/xw116qj50n96tn37lvfc6rrm0000gn/T/FiniteSets.tla
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module add_one
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module MC
Starting... (2019-12-23 17:27:10)
Error: TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a java.lang.NullPointerException
java.lang.NullPointerException
	at tlc2.tool.impl.SpecProcessor.processSpec(SpecProcessor.java:346)
	at tlc2.tool.impl.SpecProcessor.<init>(SpecProcessor.java:157)
	at tlc2.tool.impl.Spec.<init>(Spec.java:121)
	at tlc2.tool.impl.Tool.<init>(Tool.java:126)
	at tlc2.tool.impl.Tool.<init>(Tool.java:121)
	at tlc2.tool.impl.Tool.<init>(Tool.java:116)
	at tlc2.TLC.process(TLC.java:930)
	at tlc2.TLC.main(TLC.java:247)

Finished in 00s at (2019-12-23 17:27:10)
```

# What have I learned?

I failed to model check a "hello world" example, except while using the UI. The
developers have told me (through telling others) that I should not try and
instead use the UI. The command line script seems like it should work, but
unstated assumptions in the file formats and organization that I missed caused
a null pointer and there is no reasonable error message. The UI-generated files
also don't seem to work well with the CLI as I expect it would be used.
