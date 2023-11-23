# Title

Replace `Title` with the title of your project, and *rewrite* this markdown file to describe the following:

1. The topic of your project. State the relevant background, definitions, and theorems, using natural language. Add any necessary references.
2. The structure of the lean project itself. How is your code organized?
3. The main definitions you constructed and/or theorems you formalized, and where they can be found in your code.
4. Any other relevant information.

# Using this template

To use this template, go to its [github page](https://github.com/Formal-Mathematics/final_project_template), and click the green "Use this template" button near the top-right of the page.
Then follow the instructions to create a new repository using the template.
Once you have done this, you should have a repository in your github account with some name that I will assume to be `final_project`.
Clone this repository to your local machine using `git clone` to start working on your project.

# Updating Mathlib

This template repository depends on `mathlib4`.
When you first clone the repository, you will need to run

```bash
lake exe cache get
```

in the main directory of the project to obtain the `mathlib4` cache.

If you need to update mathlib, you can do so by running

```bash
lake update mathlib
```

in the main directory of the project.
Alternatively, you can use the lean4 vscode extension to do this for you.
To use the vscode extension, click the "forall" icon at the top-right of the editor window when you have a lean4 file from your project open. 

# Project structure

This template is set up with a `Project.lean` file in the root directory, and a `Project` folder where additional lean files can be placed.
If you decide to change the name `Project` to something else, you will need to edit the `lakefile.lean` file accordingly.

# Submitting your final project

To submit your final project, just send the instructor the URL of your project's github repository.
If you set the repository to be *private*, then you may need to grant the instructor access to the repository.

**NOTE:** It is recommended that you make your project's repository public unless you are sufficiently experienced with github's user permission system.