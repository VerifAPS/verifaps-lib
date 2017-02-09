# Geteta 

Generalized Test Tables ensures safety in automation software.

## Download

These are jar files include all dependencies:

* 0.4.0: [geteta-0.3.0.jar](downloads/geteta-0.4.0.jar)
  * Counter examples in the semantic of traces in the test table
* 0.3.0: [geteta-0.3.0.jar](downloads/geteta-0.3.0.jar)
  * enum support tested and fixed
* 0.2.2-beta: [geteta-0.2.2-beta.jar](downloads/geteta-0.2.2-beta.jar)
  * better nuxmv output parser
* 0.2.1-beta: [geteta-0.2.1-beta.jar](downloads/geteta-0.2.1-beta.jar)
  * Internal changes
* 0.2.0: [geteta-0.2.0.jar](downloads/geteta-0.2.0.jar)

## From Source

```
$ git clone https://github.com/VerifAPS/geteta.git 
$ mvn assembly:single
```

## Getting started

Ensure, that you have installed [nuXmv](http://nuxmv.fbk.eu).
You need to set the `NUXMV` environment variable to the nuXmv executable.

```
export NUXMV=/home/weigl/work/nuXmv-1.1.1-Linux/bin/nuXmv
```

After this, you can call geteta with:

```
java -jar geteta-${project.version}.jar -c program.st -t testtable.xml [-x]
```

With `-x` , geteta writes the output in an XML format.

[More information about test table format.](intro.md) 
