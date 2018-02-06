Setting Up to Use Git
=====================

Git and Distributed Software Development
----------------------------------------

Large systems built by hundreds or thousands of developers around the world

* Challenge is to coordinate many changes being made around the globe
* Often have a shared, reference copy that everyone shares (e.g., on GitHub)
* Can’t really have thousand of people making uncontrolled changes
* Rather, everyone has entire history of whole project on local machine
* Anyone can edit their own copy
* Anyone with privileges can push local changes back to central version
* Anyone can ask central developers to “pull” local changes into central repo
* Anyone can register an “issue” with main developers
* Updates made to central repo can then be “pulled” down to local versions
* But git won’t overwrite local changes -- it will say “there’s a conflict”

Setting Up
----------

Let’s make sure everyone is set up with git and up-to-date copy of cs-dm repo

* Open a terminal window [check; if not, install MSYS2 per instructions]
* Run “git” command -- does it run? [check; if not, install git]
* Change into directory you’re using for this class [advice, no spaces; check?]
* List files in this directory; ls.
* Rename any current cs-dm directory to cs-dm.old
* Clone current cs-dm directory
* Rename to cs-dm-reference; you will NOT make local changes here
* Clone current cs-dm directory again; rename to cs-dm-hw3
* Open cs-dm-hw3/dafny folder in VS Code; you’re set to do next HW

A Demo
------

Let’s see how git works; I will fix errors in code; I will push; you will pull; that’s it!

* Point browser at cs-dm-reference/notes/_build/html/index.html
* Open separate browser window on GitHub repo
* Let’s look at the issues; and fix them!
* In notes, let’s find mistake
* Now I will fix it, rebuild the HTML and PDF files, and push an update to GitHub
* Now you should cd into cs-dm-reference directory (the one you won’t edit)
* Do a git pull to pull the changes now on GitHub into your local repo
* And refresh browser to display the now updated HTML files!
* Note: You should do a git pull in each copy of the repo needing an update
