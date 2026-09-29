import VersoBlog
open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html lang="en">
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="dark"/>
          <link rel="icon" href="static/favicon.ico" sizes="any"/>
          <link rel="icon" type="image/png" sizes="32x32" href="static/favicon-32x32.png"/>
          <link rel="icon" type="image/png" sizes="16x16" href="static/favicon-16x16.png"/>
          <link rel="apple-touch-icon" sizes="180x180" href="static/apple-touch-icon.png"/>
          <link rel="preconnect" href="https://fonts.googleapis.com"/>
          <link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Chakra+Petch:wght@400;500;600;700&display=swap"/>
          <title>{{ (← param (α := String) "title") }} " — EpsilonEridani"</title>
          {{← builtinHeader }}
          <link rel="stylesheet" href="static/style.css"/>
          <script src="static/site.js" defer="defer"></script>
        </head>
        <body>
          <header class="site-nav">
            <div class="nav-inner">
              <a class="brand" href=".">"EpsilonEridani"</a>
              <nav class="nav-links">
                <a href=".">"Home"</a>
                <a href="statistics">"Statistics"</a>
                <a href="progress">"Progress"</a>
                <a href="about">"About"</a>
                <a href="https://github.com/eic/EpsilonEridani">"GitHub"</a>
              </nav>
            </div>
          </header>
          <main>
            {{ (← param "content") }}
          </main>
          <footer class="site-footer">
            <div class="foot-inner">
              <p class="foot-tag">"Let’s formalize lots of physics."</p>
              <ul class="foot-links">
                <li><a href="https://github.com/eic/EpsilonEridani">"EpsilonEridani"</a></li>
                <li><a href="https://github.com/eic/EpsilonEridaniRoadmaps">"EpsilonEridaniRoadmaps"</a></li>
                <li><a href="https://github.com/eic/EpsilonEridaniReview">"EpsilonEridaniReview"</a></li>
              </ul>
              <p class="foot-legal">"AI-authored Lean physics · Apache-2.0"</p>
            </div>
          </footer>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do
    return {{
      <div class="frontpage">
        <section class="hero">
          <div class="hero-copy">
            <h1 class="hero-title">"EpsilonEridani"</h1>
            <p class="hero-tag">"Let’s formalize lots of physics."</p>
            <p class="hero-sub">"AI-authored Lean formalizations of the physics of the Electron-Ion Collider — from scattering kinematics to QCD — directed by human-owned roadmaps and gated by open, adversarial review."</p>
            <div class="cta-row">
              <a class="cta" href="https://github.com/eic/EpsilonEridani">"Explore the code →"</a>
              <a class="cta secondary" href="docs/">"Read the docs →"</a>
            </div>
          </div>
        </section>

        <section class="pillars">
          <div class="pillar">
            <h3>"Humans own the roadmap"</h3>
            <p>"Physicists set the targets — nucleon spin, hadron mass, gluon saturation, 3D imaging — in a separate, human-reviewed roadmap repository. People choose the physics."</p>
          </div>
          <div class="pillar">
            <h3>"AIs write the code"</h3>
            <p>"AI agents formalize kinematics, symmetries and the relations between observables in Lean and open pull requests — every statement machine-checked, no sorries, no stray axioms."</p>
          </div>
          <div class="pillar">
            <h3>"Open review gates everything"</h3>
            <p>"AI reviewers judge each PR against fixed, open-source rubrics — correctness, reuse, API, naming, generality — and hunt for mis-formalized physics before it can merge."</p>
          </div>
        </section>

        <section class="band roadmap">
          <h2 class="section-title">"On the roadmap"</h2>
          <div class="cards four">
            <div class="card"><h3>"Universal covers"</h3></div>
            <div class="card"><h3>"The Jacobian challenge"</h3></div>
            <div class="card"><h3>"Reductive algebraic groups"</h3></div>
            <div class="card"><h3>"Partial differential equations"</h3></div>
          </div>
        </section>

        <section class="band growth">
          <h2 class="section-title">"Growing fast"</h2>
          <a class="growth-link" href="statistics">
            <img class="growth-img" src="static/loc-epsiloneridani.svg"
                 alt="EpsilonEridani: lines of Lean by date"/>
            <span class="growth-cta">"See the statistics →"</span>
          </a>
        </section>

        <section class="band repos">
          <h2 class="section-title">"Three repositories"</h2>
          <div class="cards three">
            <a class="card repo" href="https://github.com/eic/EpsilonEridani">
              <h3>"EpsilonEridani"</h3>
              <p>"The AI-authored Lean formalization of the physics."</p>
            </a>
            <a class="card repo" href="https://github.com/eic/EpsilonEridaniRoadmaps">
              <h3>"EpsilonEridaniRoadmaps"</h3>
              <p>"The human-controlled roadmaps that direct the work."</p>
            </a>
            <a class="card repo" href="https://github.com/eic/EpsilonEridaniReview">
              <h3>"EpsilonEridaniReview"</h3>
              <p>"The review rubrics and the machinery that runs review."</p>
            </a>
          </div>
        </section>

        <section class="band taste">
          <h2 class="section-title">"A taste of the physics"</h2>
          <p class="taste-note">"One-loop asymptotic freedom, the SU(3) adjoint Casimir, and DVCS momentum transfer — each example is checked against the library when this page is built."</p>
          <div class="carousel">
            <button class="carousel-arrow prev" type="button" aria-label="Previous example">"‹"</button>
            <div class="carousel-track">
              {{← param "content" }}
            </div>
            <button class="carousel-arrow next" type="button" aria-label="Next example">"›"</button>
          </div>
        </section>

        <section class="band credit">
          <h2 class="section-title">"Built on Tau Ceti"</h2>
          <p class="credit-note">"EpsilonEridani is built on " <a href="https://github.com/TauCetiProject/TauCeti">"Tau Ceti"</a> ", the open-source project whose AI-driven formalization and review machinery it extends from mathematics to phenomenological physics."</p>
        </section>
      </div>
    }}, id⟩
