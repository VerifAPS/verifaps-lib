pipeline {
  agent {
    node {
      label 'Gentzen'
    }

  }
  stages {
    stage('Build') {
      agent {
        docker {
          image 'wadoon/verifaps-test:latest'
        }

      }
      steps {
        sh 'gradle classes'
      }
    }
    stage('Build-Test') {
      agent {
        docker {
          image 'wadoon/verifaps-test:latest'
        }

      }
      steps {
        sh 'gradle testClasses'
      }
    }
    stage('Check') {
      agent {
        docker {
          image 'wadoon/verifaps-test:latest'
        }

      }
      steps {
        sh 'gradle --continue -parallel --build-cache check'
      }
    }
    stage('Sonarqube') {
      agent {
        docker {
          image 'wadoon/verifaps-test:latest'
        }

      }
      steps {
        sh '''gradle sonarqube \\                                                                                                           130 / git:develop / 18:40:25
  -Dsonar.projectKey=VerifAPS_verifaps-lib \\
  -Dsonar.organization=verifaps \\
  -Dsonar.host.url=https://sonarcloud.io -Dsonar.branch.name=develop \\
  -Dsonar.login=661de2898437c19b0efc976227e55b63d09d9ea5 --parallel'''
      }
    }
  }
}