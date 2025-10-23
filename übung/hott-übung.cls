% Vorlage von Lukas Stoll und Fabian Endres, verändert von Felix Cherubini

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{uebung}[2013/03/29 LaTeX class]

\LoadClass[a4paper]{scrartcl}

\RequirePackage[utf8]{inputenc}
%\RequirePackage[ngerman]{babel}
\RequirePackage{enumerate}
\RequirePackage[shortlabels]{enumitem}
\RequirePackage[symbol]{footmisc}
\RequirePackage{amsmath,amsthm,amssymb,amscd,color,graphicx,environ}
\RequirePackage{mathtools}
\RequirePackage[protrusion=true,expansion=true]{microtype}
\RequirePackage{multicol}
\RequirePackage{xspace}
\RequirePackage{wrapfig}
\RequirePackage{hyperref}
\RequirePackage{tikz}
  \usetikzlibrary{babel,cd}

\RequirePackage{lmodern}

\RequirePackage{geometry}
\geometry{tmargin=2.0cm,bmargin=2cm,lmargin=2.5cm,rmargin=2.5cm}

\setlength\parskip{\medskipamount}
\setlength\parindent{0pt}

\newcounter{blattnummer}
\newlength{\titleskip}
\setlength{\titleskip}{1.5em}
\newenvironment{blatt}{
  \clearpage
  \thispagestyle{empty}
  Universität Augsburg \hfill Felix Cherubini \\
  Lehrstuhl für Algebra und Zahlentheorie \hfill Lukas Stoll \\
  Wintersemester 2025/26

  \begin{center}\Large \textbf{Übungsblatt \theblattnummer{} zur Homotopietypentheorie} \\[1em]
  \end{center}
  \vspace{\titleskip}
}{}


\newlength{\aufgabenskip}
\setlength{\aufgabenskip}{1.4em}
\newcounter{aufgabennummer}
\newenvironment{aufgabe}[1]{
  \addtocounter{aufgabennummer}{1}
  \vspace{10pt}
  \textbf{Aufgabe \theaufgabennummer} \emph{#1} \par
}{\par\vspace{\aufgabenskip}}

\newenvironment{bonus}[1][]{
  \vspace{10pt}
  \textbf{Bonusaufgabe} \emph{{#1}}\par
}{\par\vspace{\aufgabenskip}}

\clubpenalty=10000
\widowpenalty=10000
\displaywidowpenalty=10000

\RequirePackage{../util/hott}
